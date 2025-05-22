use std::{borrow::Cow, cell::RefCell, collections::{hash_map::Entry, BTreeMap, HashMap, HashSet}, rc::Rc};
use heck::ToSnakeCase;
use proc_macro2::{Span, TokenTree};
use quote::{ToTokens, TokenStreamExt};
use syn::{parse_quote, punctuated::Punctuated, spanned::Spanned, AngleBracketedGenericArguments, Attribute, Block, Fields, FnArg, GenericArgument, GenericParam, Generics, Ident, ImplItem, ImplItemFn, Item, ItemConst, ItemEnum, ItemExternCrate, ItemFn, ItemForeignMod, ItemImpl, ItemMacro, ItemMod, ItemStatic, ItemStruct, ItemTrait, ItemTraitAlias, ItemType, ItemUnion, ItemUse, Lit, LitStr, Meta, MetaList, Pat, Path, PathArguments, PathSegment, ReturnType, Signature, Token, TraitItemFn, Type, TypePath, Visibility};
use crate::{instantiate::Instantiatable, types::{map_type_paths, TypeEnv, TypeEnvBuilder}, CppWriter};
use super::{Result, Error, types};

const META_TYPE_NAME: &'static str = "_Type";

enum WellKnown {
    Sized,
    Copy,
}

enum ZngurAttribute {
    BindTo,
    WellKnown(Vec<WellKnown>),
    CppValue(MetaList),
    RustValue(MetaList),
    CppRef(MetaList),
}

#[derive(Debug, Clone, Copy)]
enum CppPassingStyle { Ref, Value }

enum Out {
    String(String),
    Line(usize, Vec<Out>),
    LayoutOf(Type),
}
impl Into<String> for Out {
    fn into(self) -> String {
        match self {
            Out::String(s) => s,
            Out::Line(indent, outs) => {
                let indent = (0..indent).map(|_| "    ").collect::<Vec<_>>().join("");
                let args = outs.into_iter().map(|out| out.into()).collect::<Vec<String>>().join("");
                format!("{}{}\n", indent, args)
            }
            Out::LayoutOf(_) => format!("#layout(size = ?, align = ?)")
        }
    }
}
impl From<&str> for Out { fn from(value: &str) -> Self { Out::String(value.to_string()) } }
impl From<String> for Out { fn from(value: String) -> Self { Out::String(value) } }

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ImplKey(Option<Path>, Type);
impl ImplKey {
    fn with_path(modpath: Option<Path>, p: &Path) -> Self {
        Self::new(modpath, Self::path_to_ty(p.clone()))
    }
    fn ident_generics_to_ty(ident: &Ident, generics: &Generics) -> Type {
        let tys = generics.type_params().collect::<Punctuated<_, Token![,]>>();
        if tys.is_empty() {
            Self::path_to_ty(ident.clone().into())
        } else {
            return parse_quote!(#ident<#tys>);
        }
    }
    fn with_item_enum(cratepath: Option<Path>, item: &ItemEnum) -> Self {
        Self::new(cratepath, Self::ident_generics_to_ty(&item.ident, &item.generics()))
    }
    fn with_item_struct(cratepath: Option<Path>, item: &ItemStruct) -> Self {
        Self::new(cratepath, Self::ident_generics_to_ty(&item.ident, &item.generics()))
    }
    fn with_item_impl(cratepath: Option<Path>, item: &ItemImpl) -> Result<Self> {
        Ok(Self::new(cratepath, Self::self_ty_to_type(&*item.self_ty)?))
    }
    fn with_type(cratepath: Option<Path>, ty: &Type) -> Self {
        Self::new(cratepath, ty.clone())
    }

    fn path_to_ty(path: Path) -> Type {
        Type::Path(TypePath { qself: None, path })
    }
    fn new(cratepath: Option<Path>, ty: Type) -> Self {
        Self(cratepath, ty)
    }
    pub fn as_mod_path(&self) -> Vec<String> {
        let mut ret = self.0.as_ref().map(|mp| mp.segments.iter().map(|s| s.to_token_stream().to_string()).collect::<Vec<_>>()).unwrap_or_default();
        ret.push(self.1.to_token_stream().to_string());
        ret
    }
    fn self_ty_to_type(self_ty: &Type) -> Result<Type> {
        let span = self_ty.span();
        let syn::Type::Path(type_path) = &self_ty else { return Err(Error::new(span, "invalid type".into())); };
        for seg in &type_path.path.segments {
            let PathSegment { ident, arguments } = seg;
            match arguments {
                PathArguments::None => {
                    return Ok(Self::path_to_ty(ident.clone().into()));
                },
                PathArguments::AngleBracketed(args) if ident == META_TYPE_NAME && args.args.len() == 1 => {
                    if let GenericArgument::Type(ty) = args.args.first().unwrap() {
                        return Ok(ty.clone())
                    }
                }
                PathArguments::AngleBracketed(args) => {
                    let tys = args.args.iter().filter_map(|arg| match arg {
                        GenericArgument::Type(ty) => Some(ty),
                        _ => None,
                    }).collect::<Punctuated<_, Token![,]>>();
                    if tys.is_empty() {
                        return Ok(Self::path_to_ty(ident.clone().into()));
                    } else {
                        return Ok(parse_quote!(#ident<#tys>));
                    }
                }
                _ => continue
            }
        }
        Err(Error::new(span, "invalid argument".into()))
    }


}

struct ZngWriter {
    indent_level: usize,
    lines: RefCell<Vec<Out>>,
    current_line: RefCell<Vec<Out>>,
    disabled: bool,
    skip_artifacts: bool,
}
impl ZngWriter {
    fn new(skip_artifacts: bool) -> Self { Self {
        indent_level: 0,
        lines: Default::default(),
        current_line: Default::default(),
        disabled: false,
        skip_artifacts,
    } }
    fn wl(&mut self, out: Out) {
        if self.disabled { return; }
        self.w(out);
        let mut output = vec![];
        std::mem::swap(&mut output, &mut self.current_line.borrow_mut());
        let out = Out::Line(self.indent_level, output);
        self.lines.borrow_mut().push(out);
    }
    fn w(&mut self, out: Out) {
        if self.disabled || (!matches!(out, Out::LayoutOf(..)) && self.skip_artifacts) { return; }
        self.current_line.borrow_mut().push(out);
    }
    fn layout(&mut self, ty_str: String) {
        if self.disabled { return; }
        let ty: syn::Type = syn::parse_str(&ty_str).expect(&format!("failed to parse layout type '{}'", ty_str));
        self.wl(Out::LayoutOf(ty));
    }
    fn needed_layouts(&self) -> Vec<(Type, usize, usize)> {
        let mut layouts = vec![];
        for (n, line) in self.lines.borrow().iter().enumerate() {
            if let Out::Line(indent, segs) = line {
                if let (Some(Out::LayoutOf(x)), 1) = (segs.first(), segs.len()) {
                    layouts.push((x.clone(), n, *indent));
                }
            }
        }
        layouts
    }
    fn output(&mut self) -> Vec<String> {
        let mut lines = vec![];
        std::mem::swap(&mut lines, &mut *self.lines.borrow_mut());
        lines.into_iter().map(|o| Into::<String>::into(o)).collect::<Vec<_>>()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TransferType { Import(Option<Vec<String>>), Export, Expose }

fn is_crate_mod_attribute(item_mod_attr: &Attribute) -> bool {
    match &item_mod_attr.meta {
        Meta::Path(p) if p.is_ident("crate") => true,
        _ => false,
    }
}

pub fn remove_semicolon(token_stream: proc_macro2::TokenStream) -> Result<proc_macro2::TokenStream> {
    let span = token_stream.span();
    let mut tokens = token_stream.into_iter().collect::<Vec<_>>();
    match tokens.pop() {
        Some(TokenTree::Punct(p)) if p.as_char() == ';' => Ok(()),
        _ => Err(Error::new(span, "expected semicolon".into()))
    }?;
    Ok(tokens.into_iter().collect())
}

fn extract_transfer_type_from_token_stream(token_stream: proc_macro2::TokenStream) -> Result<(proc_macro2::TokenStream, Option<TransferType>)> {
    let mut transfer_type = None;
    let mut result = Ok(false);
    let mut tokens = token_stream.into_iter().collect::<Vec<_>>();
    let mut filtered_tokens: proc_macro2::TokenStream = tokens.windows(2).scan(&mut result, |skip, trees| {
        if matches!(skip, Ok(true)) {
            **skip = Ok(false);
            Some(None)
        } else {
            match (trees.get(0), trees.get(1)) {
                (hash_tt@Some(TokenTree::Punct(p)), tt) if p.as_char() == '#' => {
                    if let Some(TokenTree::Group(g)) = transfer_type.is_none().then_some(tt).flatten() {
                        let group_id = g.stream().into_iter().next().and_then(|tt| match tt {
                            TokenTree::Ident(i) => Some(i),
                            _ => None,
                        });
                        match group_id {
                            Some(id) if id == "expose" => {
                                **skip = Ok(true);
                                transfer_type = Some(TransferType::Expose);
                                Some(None)
                            }
                            Some(id) if id == "export" => {
                                **skip = Ok(true);
                                transfer_type = Some(TransferType::Export);
                                Some(None)
                            }
                            Some(id) if id == "import" => {
                                **skip = Ok(true);
                                if let Ok(MetaList { tokens, .. }) = syn::parse2::<MetaList>(g.stream()) {
                                    #[derive(Debug)]
                                    struct LitStrList(Punctuated<LitStr, Option<Token![,]>>);
                                    impl syn::parse::Parse for LitStrList {
                                        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                                            Ok(Self(Punctuated::parse_terminated(input)?))
                                        }
                                    }
                                    if let Ok(list) = syn::parse2::<LitStrList>(tokens.clone()) {
                                        let cpp_lines = list.0.into_iter().map(|l| l.value()).collect::<Vec<_>>();
                                        transfer_type = Some(TransferType::Import(Some(cpp_lines)))
                                    } else {
                                        match super::cppwriter::cpp::CppParser::parse(tokens) {
                                            Err(e) => {
                                                **skip = Err(e);
                                                return None;
                                            },
                                            Ok(cpp_lines) => {
                                                transfer_type = Some(TransferType::Import(Some(vec![cpp_lines])))
                                            }
                                        }
                                    }
                                } else {
                                    transfer_type = Some(TransferType::Import(None));
                                }
                                Some(None)
                            }
                            _ => {
                                **skip = Ok(false);
                                Some(hash_tt.cloned())
                            }
                        }
                    } else {
                        **skip = Ok(false);
                        Some(hash_tt.cloned())
                    }
                }
                (tt, _) => Some(tt.cloned())
            }
        }
    }).filter_map(|i| i).collect();
    result?;
    if let Some(last) = tokens.pop() {
        filtered_tokens.append(last);
    }
    Ok((filtered_tokens, transfer_type))
}

fn get_bind_path(attrs: &Vec<Attribute>) -> Option<Path> {
    let mut ret = None;
    attrs.iter().for_each(|attr| {
        match &attr.meta {
            Meta::List(meta_list) if meta_list.path.is_ident("bind_to") => {
                let toks = &meta_list.tokens;
                ret = Some(parse_quote! { #toks });
            }
            _ => (),
        };
    });
    ret
}

fn strip_docs_from_attributes(attrs: Vec<Attribute>) -> Vec<Attribute> {
    attrs.into_iter().filter(|a| {
        if let Meta::NameValue(nv) = &a.meta {
            !nv.path.is_ident("doc")
        } else {
            true
        }
    }).collect()
}
fn extract_transfer_type_from_attributes(attrs: Vec<Attribute>) -> Result<(Vec<Attribute>, Option<TransferType>)> {
    let mut ty = None;
    let mut span = Span::call_site();
    let attrs = attrs.into_iter().filter_map(|attr| {
        span = attr.span();
        if attr.meta.path().is_ident("expose") {
            if ty.is_none() { ty = Some(TransferType::Expose); }
            None
        } else if attr.meta.path().is_ident("export") {
            if ty.is_none() { ty = Some(TransferType::Export); }
            None
        } else if attr.meta.path().is_ident("import") {
            if ty.is_none() { ty = Some(TransferType::Import(None)); }
            None
        } else {
            Some(attr)
        }
    }).collect::<Vec<_>>();
    Ok((attrs, ty))
}
fn extract_cpp_template_args(attrs: Vec<Attribute>) -> Result<(Vec<Attribute>, Vec<LitStr>)> {
    // Impl blocks either have no attributes or a simple `#[cpp_template(...)]` attribute
    let mut cpp_meta_list_args = None;
    let attrs = attrs.into_iter().filter_map(|attr| match &attr.meta {
        Meta::List(meta_list) if meta_list.path.is_ident("cpp_template") => {
            cpp_meta_list_args = Some(meta_list.parse_args_with(Punctuated::<LitStr, syn::Token![,]>::parse_terminated));
            None
        }
        _ => Some(attr),
    }).collect::<Vec<_>>();
    if let Some(attr) = attrs.first() {
        return Err(Error::new(attr.span(), "unexpected attribute".into()));
    }
    let template_args = cpp_meta_list_args.transpose()?.map_or_else(Vec::new, |lits|
        lits.into_iter().map(|l| l).collect());
    Ok((attrs, template_args))
}


#[derive(Debug)]
struct Specialization {
    seq_num: usize,
    path: Vec<Ident>,
    args: Rc<Vec<Type>>,
    modpath: Rc<Vec<String>>,
    real_modpath: Rc<Option<Path>>,
}
// these specialzations are needed to ignore `seq_num`
impl Eq for Specialization {}
impl PartialEq for Specialization { fn eq(&self, other: &Self) -> bool { self.path == other.path && self.args == other.args && self.modpath == other.modpath && self.real_modpath == other.real_modpath } }
impl std::hash::Hash for Specialization { fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.path.hash(state); self.args.hash(state); self.modpath.hash(state); self.real_modpath.hash(state); } }
impl Ord for Specialization {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}
impl PartialOrd for Specialization {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.path.partial_cmp(&other.path) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.args.iter().map(|a| a.to_token_stream().to_string()).collect::<Vec<_>>().partial_cmp(
            &other.args.iter().map(|a| a.to_token_stream().to_string()).collect()) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.modpath.partial_cmp(&other.modpath)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)] 
pub enum ParseMode {
    TypeCheck,
    Generate,
}

enum Inst {
    Enum(ItemEnum, Option<ItemImpl>, Option<HashSet<Ident>>),
    Struct(ItemStruct, Option<ItemImpl>, Vec<ZngurAttribute>, Option<HashSet<Ident>>),
}

struct ParseState {
    n: usize,
    modstack: RefCell<Vec<(
        String,
        HashSet<String>,
        HashSet<String>,
        bool,
    )>>,
    impls: HashMap<ImplKey, ItemImpl>,
    structs_that_bind: HashMap<Ident, Path>,
    prelude_types: Rc<BTreeMap<Ident, Vec<Ident>>>,
    cpp_writer: Option<CppWriter>,
    specializations: Option<HashMap<Ident, HashSet<Specialization>>>,
    has_generated: bool,
    mode: ParseMode,
    bind_traits: Vec<ItemTrait>,
    deferred_instantiated_items: Option<Vec<Inst>>,
    type_env: Option<TypeEnv>,
    /// need to ensture specialzations are emitted in a consistent order
    specialzation_counter: usize,
}
impl ParseState {
    fn fully_qualify_path(&self, mut p: Path, lts: Option<&HashSet<Ident>>) -> Path {
        let is_std = p.segments.first().map(|s| s.ident == "std").unwrap_or_default();
        if is_std {
            p.leading_colon = Some(Token![::](p.span()));
            parse_quote!{ #p }
        } else {
            let key = ImplKey::with_path(self.cratepath(false), &p);
            if self.impls.get(&key).is_some() { p } else {
                let mut segments = p.segments.into_iter().collect::<Vec<_>>();
                if let Some(mut s) = segments.pop() {
                    s.arguments = match s.arguments {
                        PathArguments::AngleBracketed(mut args) => {
                            args.args = args.args.into_iter().filter_map(|a|
                                match a {
                                    GenericArgument::Type(ty) =>
                                        Some(GenericArgument::Type(
                                            types::map_type_paths_and_lifetimes(ty, &mut |mut tp| {
                                                tp.path = self.fully_qualify_path(tp.path, lts);
                                                tp
                                            }, lts)
                                        )),
                                    GenericArgument::Lifetime(lt) => {
                                        match lts {
                                            Some(list) if list.contains(&lt.ident) =>
                                                Some(GenericArgument::Lifetime(lt)),
                                            _ => None,
                                        }
                                    }
                                    x => Some(x),
                                }
                            ).collect();
                            if args.args.is_empty() {
                                PathArguments::None
                            } else {
                                PathArguments::AngleBracketed(args)
                            }
                        }
                        x => x
                    };
                    segments.push(s);
                }
                p.segments = segments.into_iter().collect();
                if let Some(ptype) = p.segments.last().and_then(|s| self.prelude_types.get(&s.ident)) {
                    if ptype.is_empty() { p } else {
                        let modpath: Punctuated<_, Token![::]> = ptype.clone().into_iter().collect();
                        let newpath: Path = parse_quote!{ #modpath::#p };
                        self.fully_qualify_path(newpath, lts)
                    }
                } else {
                    p
                }
            }
        }
    }
    fn collect_specialization(&mut self, type_path: TypePath) -> TypePath {
        let TypePath { qself, path } = type_path;
        if let Some(seg) = path.segments.last() {
            if let PathArguments::AngleBracketed(args) = &seg.arguments {
                let path = match self.prelude_types.get(&seg.ident) {
                    Some(path) => Cow::Borrowed(path),
                    None => Cow::Owned(self.modpath().iter().map(|p| Ident::new(&p, seg.span())).collect()),
                };

                let args = Rc::new(args.args.iter().filter_map(|a| match a {
                    GenericArgument::Type(ty) => Some(self.eval_type_path(ty.clone(), None)),
                    _ => None,
                }).collect::<Vec<_>>());
                let s = Specialization {
                    path: path.to_vec(),
                    args: args.clone(),
                    modpath: Rc::new(self.modpath()),
                    real_modpath: Rc::new(self.cratepath(true)),
                    seq_num: {
                        self.specialzation_counter += 1;
                        self.specialzation_counter
                    },
                };
                if let Some(specializations) = self.specializations.as_mut() {
                    let _inserted = match specializations.entry(seg.ident.clone()) {
                        Entry::Occupied(mut occupied_entry) =>
                            occupied_entry.get_mut().insert(s),
                        Entry::Vacant(vacant_entry) => {
                            let mut set = HashSet::new();
                            set.insert(s);
                            vacant_entry.insert(set);
                            true
                        }
                    };
                    // if inserted {
                    //     // if self.prelude_types.get(&seg.ident).is_none() {
                    //         println!("added spec: `{:?}` {}<{}> `{}`",
                    //             path.iter().map(|i| i.to_token_stream().to_string()).collect::<Vec<_>>().join("::"),
                    //             seg.ident,
                    //             args.iter().map(|i| i.to_token_stream().to_string()).collect::<Vec<_>>().join(", "),
                    //             self.modpath().join("::"),
                    //         );
                    //     // }
                    // }
                }
            }
        }
        TypePath { qself, path }
    }
    fn parse_mod_ident(&self, mut item_mod: ItemMod) -> (Option<String>, ItemMod, bool) {
        let modstack_len = self.modstack.borrow().len();
        if modstack_len <= 1 { return (None, item_mod, false) };
        let mut is_crate_mod = false;
        item_mod.attrs = item_mod.attrs.into_iter().filter(|a| {
            if is_crate_mod_attribute(a) {
                is_crate_mod = true;
                false
            } else { true }
        }).collect();
        if is_crate_mod {
            let mod_path = self.modstack.borrow().iter().skip(1).map(|(s, _, _, _)| s.as_str()).collect::<Vec<_>>().join(" :: ");
            (Some(format!("crate :: {mod_path}")), item_mod, true)
        } else {
            (Some(item_mod.ident.to_string()), item_mod, false)
        }
    }
    fn modpath(&self) -> Vec<String> {
        self.modstack.borrow().iter().skip(1).map(|(id, _, _, _)| id.clone()).collect::<Vec<_>>()
    }
    fn modpath_to_cratepath(modpath: &Vec<String>) -> Option<Path> {
        if modpath.is_empty() { None } else {
            let p = modpath.iter().map(|id| Ident::new(id, Span::call_site())).collect::<Punctuated<_, Token![::]>>();
            Some(parse_quote!(#p))

        }
    }
    fn cratepath(&self, resolve_crate: bool) -> Option<Path> {
        let p: Punctuated<Ident, Token![::]> = self.modstack.borrow().iter().skip(1).map(|(id, _, _, is_crate_mod)| {
            if *is_crate_mod && resolve_crate {vec![Ident::new("crate", Span::call_site()), Ident::new(id, Span::call_site())]
            } else {
                vec![Ident::new(id, Span::call_site())]
            }
        }).flatten().collect::<Punctuated<_, _>>();
        if p.is_empty() { None } else {
            Some(parse_quote!(#p))
        }
    }
    fn gensym(&mut self) -> proc_macro2::Ident {
        self.n += 1;
        proc_macro2::Ident::new(&format!("_{}", self.n), Span::call_site())
    }
    fn push_mod(&self, item_mod: &ItemMod) {
        let is_crate_mod = item_mod.attrs.iter().any(is_crate_mod_attribute);
        self.modstack.borrow_mut().push((item_mod.ident.to_string(), Default::default(), Default::default(), is_crate_mod));
    }
    fn pop_mod(&self) -> Vec<String> {
        if let Some((_, structs, impls, _)) = self.modstack.borrow_mut().pop() {
            if self.mode == ParseMode::TypeCheck {
                impls.difference(&structs).cloned().collect::<Vec<_>>()
            } else {
                vec![]
            }
        } else {
            vec![]
        }
    }
    fn declare_type_identifier(&mut self, id: &Ident) {
        if let Some((_, ref mut structs, _, _)) = self.modstack.borrow_mut().iter_mut().last() {
            structs.insert(id.to_string());
        }
    }
    fn declare_impl(&mut self, id: &Ident) {
        if let Some((_, _, ref mut impls, _)) = self.modstack.borrow_mut().iter_mut().last() {
            impls.insert(id.to_string());
        }
    }
    fn scan(&mut self, mut item_mod: ItemMod,
        on_should_bind: &mut impl FnMut(&Ident, &Path),
        on_mod_push: &mut impl FnMut(&ItemMod, bool),
        on_mod_pop: &mut impl FnMut(&ItemMod, bool),
        on_use: &mut impl FnMut(&ItemUse),
        on_struct: &mut impl FnMut(&ItemStruct),
        on_enum: &mut impl FnMut(&ItemEnum),
        on_impl: &mut impl FnMut(ImplKey, ItemImpl)
    ) -> Result<ItemMod> {
        self.push_mod(&item_mod);
        item_mod.content = item_mod.content.map(|(b, items)| {
            let items: Vec<Item> = items.into_iter().map(|i| match i {
                Item::Mod(item_mod) => {
                    let is_crate_mod = item_mod.attrs.iter().any(is_crate_mod_attribute);
                    on_mod_push(&item_mod, is_crate_mod);
                    let item_mod = self.scan(item_mod, on_should_bind, on_mod_push, on_mod_pop, on_use, on_struct, on_enum, on_impl)?;
                    on_mod_pop(&item_mod, is_crate_mod);
                    Ok(Item::Mod(item_mod))
                },
                Item::Use(item_use) => {
                    on_use(&item_use);
                    Ok(Item::Use(item_use))
                },
                Item::Struct(item_struct) => {
                    if let Some(path) = get_bind_path(&item_struct.attrs) {
                        on_should_bind(&item_struct.ident, &path);
                    }
                    on_struct(&item_struct);
                    Ok(Item::Struct(item_struct))
                }
                Item::Enum(item_enum) => {
                    on_enum(&item_enum);
                    Ok(Item::Enum(item_enum))
                }
                Item::Impl(item_impl) if item_impl.trait_.is_none() => {
                    let key = ImplKey::with_item_impl(self.cratepath(false), &item_impl)?;
                    on_impl(key, item_impl.clone());
                    Ok(Item::Impl(item_impl))
                }
                x => Ok(x)
            }).collect::<Result<Vec<_>>>()?;
            Result::<(syn::token::Brace, Vec<syn::Item>)>::Ok((b, items))
        }).transpose()?;
        let _ = self.pop_mod();
        Ok(item_mod)
    }
    fn parse_mod(&mut self, zng_writer: &mut ZngWriter, item: ItemMod) -> Result<Option<ItemMod>> {
        self.push_mod(&item);

        if let Some(mut writer) = self.cpp_writer.take() {
            let namespace = self.modpath().into_iter().map(|s| Ident::new(&s, item.span())).collect::<Vec<_>>();
            writer.declare_generated_namespace(namespace);
            self.cpp_writer = Some(writer);
        }

        let (mod_ident, item, is_crate) = self.parse_mod_ident(item);
        if let Some(ident) = &mod_ident {
            zng_writer.wl(format!("mod {} {{", ident).into());
            zng_writer.indent_level += 1;
        }
        let ItemMod { attrs, vis, unsafety, mod_token, ident, content, semi } = item;
        let content = content.map(|(b, items)|
            items.into_iter().map(|i|
                self.parse_item(zng_writer, i, is_crate))
                    .filter_map(|v| v.transpose())
                    .collect::<Result<_>>()
                    .map(|v: Vec<Item>| (b, v))
        ).transpose()?;
        if mod_ident.is_some() {
            zng_writer.indent_level -= 1;
            zng_writer.wl("}".into());
        }
        let missing_structs = self.pop_mod();
        let content = content.and_then(|(b, mut items)| {
            let mut missing_structs: Vec<Item> = missing_structs.into_iter().map(|missing_struct| {
                let name = Ident::new(&missing_struct, Span::call_site());
                parse_quote! { struct #name; }
            }).collect::<Vec<_>>();
            items.append(&mut missing_structs);
            if is_crate {
                items.push(parse_quote! { use super::generated; });
            }

            if self.mode == ParseMode::Generate {
                let mut bind_traits = vec![];
                std::mem::swap(&mut self.bind_traits, &mut bind_traits);
                for tr in bind_traits {
                    items.push(Item::Trait(tr));
                }
            }

            if items.is_empty() { None } else {
                Some((b, items))
            }
        });
        if content.is_none() { Ok(None) } else {
            Ok(Some(ItemMod { attrs, vis, unsafety, mod_token, ident, content, semi }))
        }
    }
    fn parse_item(&mut self, zng_writer: &mut ZngWriter, item: Item, is_crate: bool) -> Result<Option<Item>> {
        Ok(match item {
            Item::Const(item_const) => self.parse_const(zng_writer, item_const)?.map(Item::Const),
            Item::Enum(item_enum) => self.parse_enum(zng_writer, item_enum, is_crate)?.map(Item::Enum),
            Item::ExternCrate(item_extern_crate) => self.parse_extern_crate(zng_writer, item_extern_crate)?.map(Item::ExternCrate),
            Item::Fn(item_fn) => self.parse_fn(item_fn)?.map(Item::Fn),
            Item::ForeignMod(item_foreign_mod) => self.parse_foreign_mod(zng_writer, item_foreign_mod)?.map(Item::ForeignMod),
            Item::Impl(item_impl) => {
                let has_imports = Self::has_imports(item_impl.items.iter())?;

                let disabled = zng_writer.disabled;
                zng_writer.disabled = true;
                let ret = self.parse_impl(zng_writer, item_impl.clone(), has_imports)?
                    .and_then(|imp| if imp.items.is_empty() { None } else { Some(Item::Impl(imp)) });
                zng_writer.disabled = disabled;

                if has_imports {
                    zng_writer.wl("extern \"C++\" {".into());
                    zng_writer.indent_level += 1;
                    let _ = self.parse_impl(zng_writer, item_impl, true)?;
                    zng_writer.indent_level -= 1;
                    zng_writer.wl("}".into());
                }
                ret
            },
            Item::Macro(item_macro) =>self.parse_macro(zng_writer, item_macro)?.map(Item::Macro),
            Item::Mod(item_mod) => self.parse_mod(zng_writer, item_mod)?.map(Item::Mod),
            Item::Static(item_static) => self.parse_static(zng_writer, item_static)?.map(Item::Static),
            Item::Struct(item_struct) => self.parse_struct(zng_writer, item_struct)?.map(Item::Struct),
            Item::Trait(item_trait) => self.parse_trait(zng_writer, item_trait)?.map(Item::Trait),
            Item::TraitAlias(item_trait_alias) => self.parse_trait_alias(zng_writer, item_trait_alias)?.map(Item::TraitAlias),
            Item::Type(item_type) =>  self.parse_type(zng_writer, item_type)?.map(Item::Type),
            Item::Union(item_union) => self.parse_union(zng_writer, item_union)?.map(Item::Union),
            Item::Use(item_use) => self.parse_use(item_use)?.map(Item::Use),
            Item::Verbatim(token_stream) => self.parse_verbatim(zng_writer, token_stream.clone())?.map(Item::Verbatim),
            x => {
                zng_writer.wl("// UNKNOWN".into());
                Some(x)
            },
        })
    }
    fn parse_const(&mut self, zng_writer: &mut ZngWriter, item: ItemConst) -> Result<Option<ItemConst>> {
        zng_writer.wl("CONST".into());
        Ok(Some(item))
    }
    fn parse_enum(&mut self, zng_writer: &mut ZngWriter, mut item_enum: ItemEnum, is_crate: bool) -> Result<Option<ItemEnum>> {
        let (attrs, transfer_type) = extract_transfer_type_from_attributes(item_enum.attrs)?;
        item_enum.attrs = attrs;

        if matches!(transfer_type, Some(TransferType::Expose)) || matches!(transfer_type, Some(TransferType::Export)) {
            let key = ImplKey::with_item_enum(self.cratepath(false), &item_enum);
            let enum_impl = self.impls.remove(&key);

            let num_generics = item_enum.generics.type_params().count();
            if num_generics == 0 {
                if is_crate {
                    item_enum.attrs.push(parse_quote! { #[repr(u32)] });
                    zng_writer.wl(format!("enum {} {{ {} }}", item_enum.ident, item_enum.variants.to_token_stream().to_string()).into());
                } else {
                    let real_modpath = self.cratepath(true);
                    write_enum(&item_enum, None, real_modpath.as_ref(), real_modpath.as_ref(), &key.as_mod_path(), enum_impl, self, zng_writer, None)?;
                }
            } else {
                if let Some(items) = self.deferred_instantiated_items.as_mut() {
                    items.push(Inst::Enum(item_enum.clone(), enum_impl, None));
                }
            }
        }

        self.declare_type_identifier(&item_enum.ident);

        if matches!(transfer_type, Some(TransferType::Expose)) {
            Ok(None)
        } else {
            Ok(Some(item_enum))
        }
    }
    fn parse_extern_crate(&mut self, zng_writer: &mut ZngWriter, item: ItemExternCrate) -> Result<Option<ItemExternCrate>> {
        zng_writer.wl("EXTERN_CRATE".into());
        Ok(Some(item))
    }
    fn parse_fn(&mut self, item: ItemFn) -> Result<Option<ItemFn>> {
        Ok(Some(item))
    }
    fn parse_foreign_mod(&mut self, zng_writer: &mut ZngWriter, item: ItemForeignMod) -> Result<Option<ItemForeignMod>> {
        zng_writer.wl("FOREIGN_MOD".into());
        Ok(Some(item))
    }
    fn has_imports<'a>(items: impl Iterator<Item = &'a ImplItem>) -> Result<bool> {
        for item in items {
            match item {
                syn::ImplItem::Fn(ImplItemFn { attrs, .. }) => {
                    for ident in attrs.iter().filter_map(|attr| attr.path().get_ident()) {
                        if ident == "import" {
                            return Ok(true);
                        }
                    }
                }
                syn::ImplItem::Verbatim(token_stream) => {
                    let token_stream = remove_semicolon(token_stream.clone())?;
                    let item_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                    if Self::has_imports(std::iter::once(&ImplItem::Fn(item_fn)))? {
                        return Ok(true);
                    }
                }
                _ => continue
            }
        }
        return Ok(false);
    }
    fn parse_impl(&mut self, zng_writer: &mut ZngWriter, item: ItemImpl, is_extern_cpp: bool) -> Result<Option<ItemImpl>> {
        let ItemImpl { attrs, defaultness, unsafety, impl_token, generics, trait_, self_ty, brace_token, items } = item;

        let (attrs, _) = extract_cpp_template_args(attrs)?;

        zng_writer.w("impl".into());
        // LT OK
        let lifetimes = generics.lifetimes().collect::<Punctuated<_, Token![,]>>();
        if !lifetimes.is_empty() {
            zng_writer.w(format!("<{}>", lifetimes.to_token_stream()).into());
        }
        zng_writer.w(format!(" ").into());
        // LT OK
        let lts = generics.lifetimes().map(|l| l.lifetime.ident.clone()).collect::<HashSet<_>>();
        let (items, corrected_trait_) = if let Some((_, path, ..)) = &trait_ {
            let mut path = self.fully_qualify_path(path.clone(), Some(&lts));
            zng_writer.w(format!("{}", path.to_token_stream()).into());
            // Special case: In zngur, the `Iterator` trait's `Item` type is not defined as an associated type.
            // To handle this, we remove any `ImplItem::Type` with the identifier `Item` and re-insert it 
            // as a generic parameter instead. This preserves compatibility.
            let items = if let Some(last) = path.segments.last_mut() {
                let items = items.into_iter().map(|i| match i {
                    ImplItem::Type(i) if i.ident == "Item" => {
                        zng_writer.w(format!("<Item = {}>", i.ty.to_token_stream()).into());
                        if matches!(last.arguments, PathArguments::None) {
                            let ty = &i.ty;
                            let args: AngleBracketedGenericArguments = parse_quote! { <#ty> };
                            last.arguments = PathArguments::AngleBracketed(args);
                        }
                        ImplItem::Type(i)
                    },
                    x => x
                }).collect::<Vec<_>>();
                items
            } else {
                items
            };
            zng_writer.w(" for ".into());
            (items, Some(path))
        } else { (items, None) };
        let span = self_ty.span();
        let mut self_ident = None;
        let mut has_self_ty = false;
        let syn::Type::Path(mut type_path) = *self_ty else { return Err(Error::new(span, "invalid type".into())); };
        type_path.path.segments = type_path.path.segments.into_iter().map(|seg| {
            let PathSegment { ident, arguments } = seg;
            let (ident, arguments) = match arguments {
                PathArguments::None => {
                    zng_writer.w(format!("{}", ident).into());
                    self_ident = Some(ident.clone());
                    has_self_ty = true;
                    Ok((ident, PathArguments::None))
                },
                PathArguments::AngleBracketed(args) if ident == META_TYPE_NAME && args.args.len() == 1 => {
                    let arg = args.args.first().unwrap();
                    zng_writer.w(format!("{}", arg.to_token_stream()).into());
                    Ok((self.gensym(), PathArguments::None))
                }
                PathArguments::AngleBracketed(args) => {
                    zng_writer.w(format!("{}<{}>", ident, args.args.to_token_stream()).into());
                    self_ident = Some(ident.clone());
                    has_self_ty = true;
                    Ok((ident, PathArguments::AngleBracketed(args)))
                }
                x => Err(Error::new(x.span(), "invalid argument".into()))
            }?;
            self.declare_impl(&ident);
            Ok(PathSegment { ident, arguments })
        }).collect::<Result<_>>()?;

        zng_writer.wl(" {".into());
        zng_writer.indent_level += 1;
        let self_ty = Box::new(syn::Type::Path(type_path));
        let items: Vec<ImplItem> = items.into_iter()
            .filter_map(|item| {
                self.parse_impl_item(zng_writer, has_self_ty.then_some(&*self_ty), item, corrected_trait_.as_ref(), is_extern_cpp, Some(&lts)).transpose()
            }).collect::<Result<_>>()?;
        zng_writer.indent_level -= 1;
        zng_writer.wl("}".into());
        if trait_.is_some() && is_extern_cpp {
            Ok(None)
        } else {
            let should_strip_docs = (self.mode == ParseMode::Generate).then_some(self_ident.as_ref()).flatten().map(|id| self.structs_that_bind.contains_key(&id)).unwrap_or_default();
            let items = if !should_strip_docs { items } else {
                items.into_iter().map(|item| {
                    if let ImplItem::Fn(mut impl_item_fn) = item {
                        impl_item_fn.attrs = strip_docs_from_attributes(impl_item_fn.attrs);
                        ImplItem::Fn(impl_item_fn)
                    } else {
                        item
                    }
                }).collect()
            };
            Ok(Some(ItemImpl { attrs, defaultness, unsafety, impl_token, generics, trait_, self_ty, brace_token, items }))
        }
    }
    fn parse_macro(&mut self, zng_writer: &mut ZngWriter, item: ItemMacro) -> Result<Option<ItemMacro>> {
        zng_writer.wl("MACRO".into());
        Ok(Some(item))
    }
    fn parse_static(&mut self, zng_writer: &mut ZngWriter, item: ItemStatic) -> Result<Option<ItemStatic>> {
        zng_writer.wl("STATIC".into());
        Ok(Some(item))
    }
    fn parse_zngur_meta_attributes(&mut self, zng_writer: &mut ZngWriter, zng_attrs: &Vec<ZngurAttribute>, template_args: Vec<(LitStr, &Ident)>) -> Result<(Option<CppPassingStyle>, bool, bool)> {
        let mut needs_layout = true;
        let mut passing_style = None;
        let mut should_bind = false;
        for zattr in zng_attrs {
            match zattr {
                ZngurAttribute::BindTo => {
                    should_bind = true;
                },
                ZngurAttribute::WellKnown(wellknown) => {
                    for w in wellknown {
                        match w {
                            WellKnown::Sized => {
                                zng_writer.wl(format!("wellknown_traits(?Sized);").into());
                                needs_layout = false;
                            }
                            WellKnown::Copy => {
                                zng_writer.wl(format!("wellknown_traits(Copy);").into());
                            }
                        }
                    }
                },
                ZngurAttribute::CppValue(meta_list) => {
                    zng_writer.wl("constructor(ZngurCppOpaqueOwnedObject);".into());
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid cpp_value token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Int(a)), Some(Lit::Str(b)), None) = (ai.next(), ai.next(), ai.next()) else {
                        return Err(Error::new(span, "invalid cpp_value token".into()))
                    }; 
                    let mut cpp_value = b.value();
                    for (v, p) in template_args.iter() {
                        cpp_value = cpp_value.replace(&format!("{{{}}}", p.to_token_stream()), &v.value());
                    }
                    zng_writer.wl(format!("#cpp_value \"{}\" \"{}\";", a.base10_digits(), cpp_value).into());
                    passing_style = Some(CppPassingStyle::Value);
                },
                ZngurAttribute::RustValue(meta_list) => {
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid rust_value token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Int(a)), Some(Lit::Str(b)), None) = (ai.next(), ai.next(), ai.next()) else {
                        return Err(Error::new(span, "invalid rust_value token".into()))
                    }; 
                    zng_writer.wl(format!("#rust_value \"{}\" \"{}\";", a.base10_digits(), b.value()).into());
                },
                ZngurAttribute::CppRef(meta_list) => {
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid cpp_ref token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Str(a)), None) = (ai.next(), ai.next()) else {
                        return Err(Error::new(span, format!("invalid cpp_ref token").into()));
                    };
                    zng_writer.wl(format!("#cpp_ref \"{}\";", a.value()).into());
                    needs_layout = false;
                    passing_style = Some(CppPassingStyle::Ref);
                },
            }
        }

        Ok((passing_style, should_bind, needs_layout))
    }
    fn parse_meta_attributes(&mut self, attrs: Vec<Attribute>) -> Result<(Vec<Attribute>, Vec<ZngurAttribute>)> {
        let mut zng_attrs = vec![];
        let attrs = attrs.into_iter().filter_map(|attr| {
            let Attribute { pound_token, style, bracket_token, meta } = attr;
            let meta = match meta {
                Meta::List(meta_list) if meta_list.path.is_ident("bind_to") => {
                    zng_attrs.push(ZngurAttribute::BindTo);
                    None
                }
                Meta::List(mut meta_list) if meta_list.path.is_ident("wellknown") => {
                    let mut wellknown = vec![];
                    meta_list.path = proc_macro2::Ident::new("derive", meta_list.path.span()).into();
                    let tokens = meta_list.tokens.to_token_stream().into_iter().collect::<Vec<_>>();
                    let mut found_index = None;
                    tokens.windows(2).enumerate().for_each(|(n, toks)| {
                        match (&toks[0], &toks[1]) {
                            (TokenTree::Punct(a), TokenTree::Ident(b)) if a.as_char() == '?' && b == "Sized" => {
                                found_index = Some(n);
                                wellknown.push(WellKnown::Sized);
                            }
                            _ => ()
                        }
                    });
                    meta_list.tokens = tokens.into_iter().enumerate().filter_map(|(n, t)|
                        if Some(n) == found_index || Some(n) == found_index.map(|n| n + 1) { None } else { Some(t) }
                    ).collect();
                    if let Ok(mut metas) = meta_list.parse_args_with(Punctuated::<Meta, syn::Token![,]>::parse_terminated) {
                        let mut has_clone = false;
                        let mut has_copy = false;
                        for meta in metas.iter() {
                            match meta {
                                Meta::Path(path) if path.is_ident("Copy") => {
                                    has_copy = true;
                                    wellknown.push(WellKnown::Copy);
                                }
                                Meta::Path(path) if path.is_ident("Clone") => {
                                    has_clone = true;
                                }
                                _ => ()
                            }
                        }
                        if has_copy && !has_clone {
                            metas.push(Meta::Path(proc_macro2::Ident::new("Clone", metas.span()).into()));
                        }
                        meta_list.tokens = metas.to_token_stream();
                    }
                    zng_attrs.push(ZngurAttribute::WellKnown(wellknown));
                    Some(Meta::List(meta_list))
                }
                Meta::List(meta_list) if meta_list.path.is_ident("cpp_value") => {
                    zng_attrs.push(ZngurAttribute::CppValue(meta_list));
                    None
                }
                Meta::List(meta_list) if meta_list.path.is_ident("rust_value") => {
                    zng_attrs.push(ZngurAttribute::RustValue(meta_list));
                    None
                }
                Meta::List(meta_list) if meta_list.path.is_ident("cpp_ref") => {
                    zng_attrs.push(ZngurAttribute::CppRef(meta_list));
                    None
                }
                x => Some(x),
            };
            meta.map(|meta| Attribute { pound_token, style, bracket_token, meta })
        }).collect::<Vec<_>>();
        Ok((attrs, zng_attrs))
    }

    fn eval_type_path(&self, ty: Type, lts: Option<&HashSet<Ident>>) -> Type {
        let real_modpath = self.cratepath(true);
        let type_env = self.type_env.as_ref();
        types::from_fully_qualified(
            types::to_fully_qualified(ty, real_modpath.as_ref(), type_env, lts),
            real_modpath.as_ref(),
            type_env, lts
        )
    }

    fn parse_struct(&mut self, zng_writer: &mut ZngWriter, mut item: ItemStruct) -> Result<Option<ItemStruct>> {
        let num_generics = item.generics.type_params().count();
        let mut bind_id = None;
        let (passing_style, is_meta_type) = if item.ident == META_TYPE_NAME {
            let span = item.fields.span();
            let (1, Some(syn::Field { ident: None, ty , .. })) = (item.fields.len(), item.fields.iter().next()) else { return Err(Error::new(span, "expects a single field".into())); };

            let ty = self.eval_type_path(ty.clone(), None);

            zng_writer.wl(format!("type {} {{", ty.to_token_stream()).into());
            zng_writer.indent_level += 1;
            let (attrs, zng_attrs) = self.parse_meta_attributes(item.attrs)?;
            item.attrs = attrs;
            let (passing_style, _, needs_layout) = self.parse_zngur_meta_attributes(zng_writer, &zng_attrs, vec![])?;
            if needs_layout && num_generics == 0 {
                zng_writer.layout(ty.to_token_stream().to_string());
            }
            let key = ImplKey::with_type(self.cratepath(false), &ty);
            if let Some(imp) = self.impls.remove(&key) {
                let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
                for item in imp.items {
                    self.parse_impl_item(zng_writer, Some(&imp.self_ty), item, trait_, false, None)?;
                }
            }
            zng_writer.indent_level -= 1;
            zng_writer.wl("}".into());
            item.ident = self.gensym();
            (passing_style, self.mode != ParseMode::TypeCheck)
        } else {
            let (attrs, zng_attrs) = self.parse_meta_attributes(item.attrs)?;
            item.attrs = attrs;

            let key = ImplKey::with_item_struct(self.cratepath(false), &item);
            let struct_impl = self.impls.remove(&key);

            let disabled = zng_writer.disabled;
            if num_generics > 0 { zng_writer.disabled = true; }
            let real_modpath = self.cratepath(true);
            let (id, passing_style) = write_struct(&item, None, real_modpath.as_ref(), real_modpath.as_ref(), struct_impl.clone(), &zng_attrs, self, zng_writer, None)?;
            zng_writer.disabled = disabled;

            bind_id = id;

            if num_generics > 0 {
                if let Some(items) = self.deferred_instantiated_items.as_mut() {
                    items.push(Inst::Struct(item.clone(), struct_impl, zng_attrs, None));
                }
            }

            (passing_style, false)
        };

        let ItemStruct { attrs, vis, struct_token, ident, generics, fields, semi_token } = item;
        self.declare_type_identifier(&ident);
        if let Some(trait_ident) = bind_id {
            Ok(Some(parse_quote! {
                #vis struct #ident(Box<dyn #trait_ident>);
            }))
        } else {
            match (fields, passing_style, is_meta_type) {
                (_, _, true) => Ok(None),
                (Fields::Unit, Some(CppPassingStyle::Ref), _) => {
                    let temp: ItemStruct = parse_quote!{ struct Tmp_(generated::ZngurCppOpaqueBorrowedObject); };
                    Ok(Some(ItemStruct { attrs, vis, struct_token, ident, generics, fields: temp.fields, semi_token }))
                }
                (Fields::Unit, Some(CppPassingStyle::Value), _) => {
                    let temp: ItemStruct = parse_quote!{ struct Tmp_(pub generated::ZngurCppOpaqueOwnedObject); };
                    Ok(Some(ItemStruct { attrs, vis, struct_token, ident, generics, fields: temp.fields, semi_token }))
                }
                (fields, _, _) =>
                    Ok(Some(ItemStruct { attrs, vis, struct_token, ident, generics, fields, semi_token }))
            }
        }
    }
    fn parse_trait(&mut self, zng_writer: &mut ZngWriter, item: ItemTrait) -> Result<Option<ItemTrait>> {
        zng_writer.wl("TRAIT".into());
        Ok(Some(item))
    }
    fn parse_trait_alias(&mut self, zng_writer: &mut ZngWriter, item: ItemTraitAlias) -> Result<Option<ItemTraitAlias>> {
        zng_writer.wl("TRAIT_ALIAS".into());
        Ok(Some(item))
    }
    fn parse_type(&mut self, zng_writer: &mut ZngWriter, item: ItemType) -> Result<Option<ItemType>> {
        zng_writer.wl("TYPE".into());
        Ok(Some(item))
    }
    fn parse_union(&mut self, zng_writer: &mut ZngWriter, item: ItemUnion) -> Result<Option<ItemUnion>> {
        zng_writer.wl("UNION".into());
        Ok(Some(item))
    }
    fn parse_use(&mut self, item: ItemUse) -> Result<Option<ItemUse>> {
        Ok(Some(item))
    }
    fn parse_verbatim(&mut self, zng_writer: &mut ZngWriter, token_stream: proc_macro2::TokenStream) -> Result<Option<proc_macro2::TokenStream>> {
        let (token_stream, transfer_type) = extract_transfer_type_from_token_stream(token_stream.clone())?;
        match transfer_type {
            Some(TransferType::Expose) => {
                let token_stream = remove_semicolon(token_stream)?;
                let item_fn: ItemFn = parse_quote! { #token_stream { unimplemented!() } };
                self.parse_sig(zng_writer, None, item_fn.sig, None)?;
                Ok(None)
            }
            Some(TransferType::Export) => {
                Ok(Some(token_stream))
            }
            Some(TransferType::Import(cpp_lines)) => {
                zng_writer.wl("extern \"C++\" {".into());
                zng_writer.indent_level += 1;
                let token_stream = remove_semicolon(token_stream)?;
                let item_fn: ItemFn = parse_quote! { #token_stream { unimplemented!() } };
                let modpath = self.modpath();
                if let Some((lines, w)) = cpp_lines.zip(self.cpp_writer.as_mut()) {
                    w.add_lines(modpath, None, None, &item_fn.sig, &lines);
                }
                let mut item_fn = if self.has_generated {
                    let sig_ident = item_fn.sig.ident;
                    let args = item_fn.sig.inputs.iter().map(|i| match i {
                        FnArg::Receiver(receiver) => receiver.self_token.to_token_stream(),
                        FnArg::Typed(pat_type) => pat_type.pat.to_token_stream(),
                    });
                    let item_fn: ItemFn = parse_quote! { #token_stream {
                        generated::#sig_ident(#(#args),*)
                    } };
                    item_fn
                } else {
                    item_fn
                };
                item_fn.sig = self.parse_sig(zng_writer, None, item_fn.sig, None)?;
                zng_writer.indent_level -= 1;
                zng_writer.wl("}".into());
                if self.mode == ParseMode::Generate {
                    let fn_ident = &item_fn.sig.ident;
                    Ok(Some(parse_quote! { pub(crate) use super::generated::#fn_ident; }))
                } else {
                    Ok(Some(item_fn.to_token_stream()))
                }
            }
            None => {
                Ok(Some(token_stream))
            }
        }
    }
    fn parse_ty(&mut self, zng_writer: &mut ZngWriter, ty: syn::Type) -> Result<syn::Type> {
        Ok(match ty {
            syn::Type::Array(type_array) => {
                zng_writer.wl("[ARRAY]".into());
                syn::Type::Array(type_array)
            }
            syn::Type::BareFn(type_bare_fn) => {
                zng_writer.wl("[BARE_FN]".into());
                syn::Type::BareFn(type_bare_fn)
            }
            syn::Type::Group(type_group) => {
                zng_writer.wl("//[GROUP]".into());
                syn::Type::Group(type_group)
            }
            syn::Type::ImplTrait(type_impl_trait) => {
                zng_writer.wl("//[IMPL_TRAIT]".into());
                syn::Type::ImplTrait(type_impl_trait)
            }
            syn::Type::Infer(type_infer) => {
                zng_writer.wl("//[INFER]".into());
                syn::Type::Infer(type_infer)
            }
            syn::Type::Macro(type_macro) => {
                zng_writer.wl("//[MACRO]".into());
                syn::Type::Macro(type_macro)
            }
            syn::Type::Never(type_never) => {
                zng_writer.wl("//[NEVER]".into());
                syn::Type::Never(type_never)
            }
            syn::Type::Paren(type_paren) => {
                zng_writer.wl("//[PAREN]".into());
                syn::Type::Paren(type_paren)
            }
            syn::Type::Path(type_path) => {
                let type_path = self.collect_specialization(type_path);
                syn::Type::Path(type_path)
            }
            syn::Type::Ptr(type_ptr) => {
                //self.wl("[PTR]");
                syn::Type::Ptr(type_ptr)
            }
            syn::Type::Reference(type_reference) => {
                //self.wl("//[REFERENCE]");
                syn::Type::Reference(type_reference)
            }
            syn::Type::Slice(type_slice) => {
                zng_writer.wl("//[SLICE]".into());
                syn::Type::Slice(type_slice)
            }
            syn::Type::TraitObject(type_trait_object) => {
                zng_writer.wl("//[TRAIT_OBJECT]".into());
                syn::Type::TraitObject(type_trait_object)
            }
            syn::Type::Tuple(type_tuple) => {
                syn::Type::Tuple(type_tuple)
            }
            syn::Type::Verbatim(token_stream) => {
                zng_writer.wl("//[TOKEN_STREAM]".into());
                syn::Type::Verbatim(token_stream)
            }
            ty => ty
        })
    }
    fn parse_impl_item(&mut self, zng_writer: &mut ZngWriter, self_ty: Option<&Type>, item: ImplItem, trait_: Option<&Path>, is_extern_cpp: bool, lts: Option<&HashSet<Ident>>) -> Result<Option<ImplItem>> {
        let self_ident = self_ty.and_then(|ty| match ty {
            Type::Path(type_path) if type_path.path.segments.len() == 1 => {
                type_path.path.segments.first().map(|s| &s.ident)
            },
            _ => None,
        });

        match item {
            ImplItem::Const(impl_item_const) => {
                zng_writer.wl("// (CONST)".into());
                Ok(Some(syn::ImplItem::Const(impl_item_const)))
            }
            ImplItem::Fn(impl_item_fn) => {
                let ImplItemFn { attrs, vis, defaultness, mut sig, block } = impl_item_fn;
                let (attrs, transfer_type) = extract_transfer_type_from_attributes(attrs)?;
                if transfer_type.as_ref().map(|t| matches!(t, TransferType::Import(..))).unwrap_or_default() {
                    Err(Error::new(block.span(), "imports cannot have an implementation".into()))
                } else if transfer_type == Some(TransferType::Export) {
                    let prev_disabled = if !is_extern_cpp { None } else { Some(zng_writer.disabled) };
                    if prev_disabled.is_some() { zng_writer.disabled = true; }
                    sig = self.parse_sig(zng_writer, self_ident, sig, lts)?;
                    sig = to_guarded_signature(sig, self.mode);
                    prev_disabled.map(|d| zng_writer.disabled = d);

                    let block: Block = if let Some(path) = (self.mode == ParseMode::Generate).then(|| self_ident.and_then(|i| self.structs_that_bind.get(i))).flatten() {
                        let mut has_receiver: bool = false;
                        let inputs = sig.inputs.iter().filter_map(|i| match i {
                            FnArg::Receiver(_) => {
                                has_receiver = true;
                                None
                            },
                            FnArg::Typed(pat_type) => {
                                Some(&pat_type.pat)
                            },
                        }).collect::<Punctuated<_, Token![,]>>();
                        let should_bind = self_ident.map(|id| self.structs_that_bind.contains_key(id)).unwrap_or_default();
                        let ident = if should_bind {
                            Cow::Owned(Ident::new(&sig.ident.to_string().to_snake_case(), sig.ident.span()))
                        } else {
                            Cow::Borrowed(&sig.ident)
                        };
                        if !has_receiver {
                            match &sig.output {
                                ReturnType::Default =>
                                    parse_quote!({ #path::#ident(#inputs) }),
                                ReturnType::Type(_, ty) => {
                                    match &**ty {
                                        Type::Path(tp) if tp.path.is_ident("Self") =>
                                            parse_quote!({ Self(Box::new(#path::#ident(#inputs))) }),
                                        _ => parse_quote!({ #path::#ident(#inputs) })
                                    }
                                }
                            }
                        } else {
                            parse_quote!({ self.0.#ident(#inputs) })
                        }
                    } else {
                        block
                    };

                    let vis = Visibility::Public(Token![pub](vis.span()));
                    Ok(Some(syn::ImplItem::Fn(ImplItemFn { attrs, vis, defaultness, sig, block })))
                } else {
                    let should_bind = self_ident.map(|id| self.structs_that_bind.contains_key(id)).unwrap_or_default();
                    if self.mode == ParseMode::Generate {
                        if should_bind {
                            panic!("{:?}", sig.ident);
                        } else {
                            let impl_item_fn = ImplItemFn { attrs, vis, defaultness, sig, block };
                            // impl_item_fn.sig.output = match impl_item_fn.sig.output {
                            //     ReturnType::Default => ReturnType::Default,
                            //     ReturnType::Type(rarrow, ty) => ReturnType::Type(rarrow, Box::new(to_guarded_type(*ty))),
                            // };
                            Ok(Some(ImplItem::Fn(impl_item_fn)))
                        }
                    } else {
                        let impl_item_fn = ImplItemFn { attrs, vis, defaultness, sig, block };
                        Ok(Some(ImplItem::Fn(impl_item_fn)))
                    }
                }
            }
            ImplItem::Type(impl_item_type) => {
                Ok(Some(syn::ImplItem::Type(impl_item_type)))
            }
            ImplItem::Macro(impl_item_macro) => {
                zng_writer.wl("// (MACRO)".into());
                Ok(Some(syn::ImplItem::Macro(impl_item_macro)))
            }
            ImplItem::Verbatim(token_stream) => {
                let (token_stream, transfer_type) = extract_transfer_type_from_token_stream(token_stream)?;
                match transfer_type {
                    Some(TransferType::Expose) => {
                        let token_stream = remove_semicolon(token_stream)?;
                        let impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                        self.parse_sig(zng_writer, self_ident, impl_fn.sig, lts)?;
                        Ok(None)
                    }
                    Some(TransferType::Export) => {
                        let should_bind = self_ident.map(|id| self.structs_that_bind.contains_key(id)).unwrap_or_default();
                        if should_bind {
                            let token_stream = remove_semicolon(token_stream)?;
                            let mut impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                            impl_fn.attrs.push(parse_quote! { #[export] });
                            self.parse_impl_item(zng_writer, self_ty, ImplItem::Fn(impl_fn), trait_, is_extern_cpp, lts)
                        } else {
                            Ok(Some(ImplItem::Verbatim(token_stream)))
                        }
                    }
                    Some(TransferType::Import(cpp_lines)) => {
                        let token_stream = remove_semicolon(token_stream)?;
                        let ImplItemFn { attrs, vis, defaultness, mut sig, block } = parse_quote! { #token_stream { unimplemented!() } };
                        let modpath = self.modpath();
                        if let Some((lines, w)) = cpp_lines.zip(self.cpp_writer.as_mut()) {
                            w.add_lines(modpath, self_ty, trait_, &sig, &lines);
                        }
                        if is_extern_cpp {
                            sig = self.parse_sig(zng_writer, self_ident, sig, lts)?;
                        }
                        if self.has_generated || self.mode == ParseMode::Generate {
                            Ok(None)
                        } else {
                            Ok(Some(ImplItem::Fn(ImplItemFn { attrs, vis, defaultness, sig, block })))
                        }
                    }
                    None => {
                        let should_bind = self_ident.map(|id| self.structs_that_bind.contains_key(id)).unwrap_or_default();
                        if should_bind {
                            let token_stream = remove_semicolon(token_stream)?;
                            let mut impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                            if self.mode == ParseMode::TypeCheck {
                                Ok(Some(ImplItem::Fn(impl_fn)))
                            } else {
                                let ident = &impl_fn.sig.ident;
                                let inputs = impl_fn.sig.inputs.iter().filter_map(|i| match i {
                                    FnArg::Receiver(_) => None,
                                    FnArg::Typed(pat_type) => Some(&pat_type.pat),
                                }).collect::<Punctuated<_, Token![,]>>();
                                impl_fn.block = parse_quote!({ self.0.#ident(#inputs) });
                                impl_fn.sig = to_guarded_signature(impl_fn.sig, self.mode);
                                Ok(Some(ImplItem::Fn(impl_fn)))
                            }
                        } else {
                            Ok(Some(ImplItem::Verbatim(token_stream)))
                        }
                    }
                }
            }
            x => {
                zng_writer.wl("// (UNKNOWN)".into());
                Ok(Some(x))
            }
        }
    }
    fn parse_sig(&mut self, zng_writer: &mut ZngWriter, self_ident: Option<&Ident>, sig: Signature, lts: Option<&HashSet<Ident>>) -> Result<Signature> {
        let inputs = sig.inputs.iter().map(|i| Ok(match i {
            FnArg::Receiver(receiver) => receiver.to_token_stream(),
            FnArg::Typed(pat_type) => {
                let ty = self.parse_ty(zng_writer, *pat_type.ty.clone())?;
                self.eval_type_path(ty, lts).to_token_stream()
            },
        })).collect::<Result<Punctuated<_, Token![,]>>>()?;
        zng_writer.w(format!("fn {}({})", sig.ident, inputs.to_token_stream()).into());
        if let ReturnType::Type(_, ty) = &sig.output {
            let ty = self.parse_ty(zng_writer, *ty.clone())?;
            zng_writer.w(match (ty, self_ident) {
                (Type::Path(TypePath { path, .. }), Some(ident)) if path.is_ident("Self") =>
                    format!(" -> {}", ident.to_token_stream()).into(),
                (ty, _) => {
                    let ty = self.eval_type_path(ty, lts);
                    format!(" -> {}", ty.to_token_stream()).into()
                }
            });
        }
        zng_writer.wl(";".into());

        Ok(sig)
    }
}

pub struct Parser {
    state: ParseState,
    zng_writer: ZngWriter,
}

impl Parser {
    pub fn new(additional_includes: &Vec<String>, prelude_types: BTreeMap<Ident, Vec<Ident>>) -> Self {
       Self::with_details(false, additional_includes, prelude_types, false, ParseMode::Generate)
    }
    pub fn with_details(has_generated: bool, additional_includes: &Vec<String>, prelude_types: BTreeMap<Ident, Vec<Ident>>, skip_artifacts: bool, mode: ParseMode) -> Self {
        let mut ret = Self {
            state: ParseState {
                has_generated,
                n: 0,
                modstack: RefCell::new(vec![]),
                impls: Default::default(),
                structs_that_bind: Default::default(),
                prelude_types: Rc::new(prelude_types),
                cpp_writer: None,
                specializations: Some(Default::default()),
                mode,
                bind_traits: vec![],
                deferred_instantiated_items: Some(Default::default()),
                type_env: None,
                specialzation_counter: 0,
            },
            zng_writer: ZngWriter::new(skip_artifacts),
        };
        if !additional_includes.is_empty() {
            ret.zng_writer.wl("#cpp_additional_includes \"".into());
            for include in additional_includes {
                ret.zng_writer.wl(include.replace("\\", "\\\\").replace("\"", "\\\"").into());
            }
            ret.zng_writer.wl("\"".into());
        }
        ret
    }
    pub fn set_cpp_writer(&mut self, mut writer: CppWriter) {
        writer.prelude_types = self.state.prelude_types.clone();
        self.state.cpp_writer = Some(writer);
    }
    pub fn take_cpp_writer(&mut self) -> Option<CppWriter> { self.state.cpp_writer.take() }
    pub fn parse(&mut self, item: ItemMod) -> Result<Vec<Item>> {
        let mut structs_that_bind = HashMap::<Ident, Path>::new();
        let mut impls = HashMap::<ImplKey, ItemImpl>::new();
        let tenv_builder = RefCell::new(if self.state.mode == ParseMode::Generate {
            Some(TypeEnvBuilder::new(&*self.state.prelude_types))
        } else { None });
        let item = self.state.scan(
            item,
            &mut|ident, path| {
                structs_that_bind.insert(ident.clone(), path.clone());
            },
            &mut |item, is_crate_mod| {
                tenv_builder.borrow_mut().as_mut().map(|e| e.do_push_mod(item, is_crate_mod));
            },
            &mut |item, is_crate_mod| {
                tenv_builder.borrow_mut().as_mut().map(|e| e.do_pop_mod(item, is_crate_mod));
            },
            &mut |item_use| {
                tenv_builder.borrow_mut().as_mut().map(|e| e.do_use(item_use));
            },
            &mut |item| {
                if item.ident != META_TYPE_NAME {
                    tenv_builder.borrow_mut().as_mut().map(|e| e.do_struct(item));
                }
            },
            &mut |item| {
                tenv_builder.borrow_mut().as_mut().map(|e| e.do_enum(item));
            },
            &mut |key, item_impl| {
                impls.insert(key, item_impl);
            }
        )?;
        if let Some(builder) = tenv_builder.take() {
            let type_env = builder.build();
            self.state.type_env = Some(type_env);
        }
        self.state.impls = impls;
        self.state.structs_that_bind = structs_that_bind;

        let items = self.state.parse_mod(&mut self.zng_writer, item)?.and_then(|item|
            item.content.map(|(_, items)| items)).unwrap_or_default();

        self.render_deferred_items()?;

        Ok(items)
    }
    pub fn output(&mut self) -> Vec<String> {
        self.zng_writer.output()
    }
    pub fn needed_layouts(&self) -> Vec<(Type, usize, usize)> {
        self.zng_writer.needed_layouts()
    }

    fn render_deferred_items(&mut self) -> Result<()> {
        if let Some((specializations, items)) = self.state.specializations.take().zip(self.state.deferred_instantiated_items.take()) {
            for inst in items {
                match inst {
                    Inst::Enum(item_enum, item_impl, lts) => {
                        let instantiated_items = get_instantiated_items(&item_enum, item_impl.as_ref(), &specializations, &mut self.state.impls)?;
                        for (item, item_impl, modpath, real_modpath, type_args) in instantiated_items {
                            write_enum(&item, Some(&type_args), self.state.cratepath(true).as_ref(), (*real_modpath).as_ref(), &modpath, item_impl, &mut self.state, &mut self.zng_writer, lts.as_ref())?;
                        }
                    }
                    Inst::Struct(item_struct, item_impl, zng_attrs, lts) => {
                        let instantiated_items = get_instantiated_items(&item_struct, item_impl.as_ref(), &specializations, &mut self.state.impls)?;
                        for (item, item_impl, _modpath, real_modpath, type_args) in instantiated_items {
                            write_struct(&item, Some(&type_args), self.state.cratepath(true).as_ref(), (*real_modpath).as_ref(), item_impl, &zng_attrs, &mut self.state, &mut self.zng_writer, lts.as_ref())?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

fn get_instantiated_items<I: Instantiatable>(item: &I, item_impl: Option<&ItemImpl>, specializations: &HashMap<Ident, HashSet<Specialization>>, impls: &mut HashMap<ImplKey, ItemImpl>) -> Result<Vec<(I, Option<ItemImpl>, Rc<Vec<String>>, Rc<Option<Path>>, HashMap<Ident, syn::Type>)>> {
    let mut instantiated_items = vec![];
    if let Some(specializations) = specializations.get(&item.ident()) {
        let mut specializations = specializations.iter().collect::<Vec<_>>();
        specializations.sort_by_key(|s| s.seq_num);
        for s in specializations.iter() {
            let params = item.generics().params.iter().filter_map(|p| match p {
                GenericParam::Type(type_param) => Some(type_param.ident.clone()),
                _ => None
            }).collect::<Vec<_>>();
            if !s.args.is_empty() && params.len() != s.args.len() {
                return Err(Error::new(item.get_span(), "invalid number of generic arguments".into()));
            }

            let cratepath = ParseState::modpath_to_cratepath(&s.modpath);
            if let Some((item, item_impl)) = item.instantiate(&params, &s.args, &cratepath, item_impl)? {
                let type_args = s.args.iter().zip(params.into_iter()).map(|(a, b)| (b, a.clone())).collect::<HashMap<_, _>>();
                let item_impl = item_impl.or_else(|| {
                    let ty =  ImplKey::ident_generics_to_ty(&item.ident(), &item.generics());
                    let mmty = map_type_paths(ty.clone(), &mut |tpath| {
                        match tpath {
                            TypePath { qself: None, path } =>
                                path.segments.first().and_then(|f| match type_args.get(&f.ident) {
                                    Some(Type::Path(tpath)) => Some(tpath.clone()),
                                    _ => None,
                               }).unwrap_or_else(|| TypePath { qself: None, path }),
                            x => x
                        }
                    });

                    let key = ImplKey::with_type(cratepath, &mmty);
                    impls.remove(&key)
                });


                instantiated_items.push((item, item_impl, s.modpath.clone(), s.real_modpath.clone(), type_args));
            }
        }
    }
    Ok(instantiated_items)
}

fn write_enum(item: &ItemEnum, type_args: Option<&HashMap<Ident, Type>>, from_full: Option<&Path>, to_full: Option<&Path>, modpath: &Vec<String>, item_impl: Option<ItemImpl>, state: &mut ParseState, zng_writer: &mut ZngWriter, lts: Option<&HashSet<Ident>>) -> Result<()> {
    let tp: Type = types::from_fully_qualified(
        types::to_fully_qualified(
            types::to_type(&item.ident, type_args),
            to_full, state.type_env.as_ref(), lts),
        from_full, state.type_env.as_ref(), lts);
    zng_writer.wl(format!("type {} {{", tp.to_token_stream()).into());
    zng_writer.indent_level += 1;
    if let Some(args) = type_args {
        zng_writer.layout(format!("{} < {} > ", item.ident, args.values().map(|ty| ty.to_token_stream().to_string()).collect::<Vec<_>>().join(", ")));
    } else {
        let is_std = modpath.first().map(|s| s == "std").unwrap_or_default();
        zng_writer.layout(if is_std {
            format!(":: {}", modpath.join(" :: "))
        } else {
            format!("{}", modpath.join(" :: "))
        });
    }
    for variant in item.variants.iter() {
        zng_writer.wl(format!("constructor {}{};", variant.ident, variant.fields.to_token_stream()).into());
    }
    if let Some(imp) = item_impl {
        let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
        for impl_item in imp.items {
            state.parse_impl_item(zng_writer, Some(&imp.self_ty), impl_item, trait_, false, None)?;
        }
    }
    zng_writer.indent_level -= 1;
    zng_writer.wl("}".into());
    Ok(())
}

fn write_struct(item: &ItemStruct, type_args: Option<&HashMap<Ident, Type>>, from_full: Option<&Path>, to_full: Option<&Path>, mut item_impl: Option<ItemImpl>, zng_attrs: &Vec<ZngurAttribute>, state: &mut ParseState, zng_writer: &mut ZngWriter, lts: Option<&HashSet<Ident>>) -> Result<(Option<Ident>, Option<CppPassingStyle>)> {
    let tp: Type = types::from_fully_qualified(
        types::to_fully_qualified(
            types::to_type(&item.ident, type_args),
            to_full, state.type_env.as_ref(), lts),
        from_full, state.type_env.as_ref(), lts);
    zng_writer.wl(format!("type {} {{", tp.to_token_stream()).into());
    zng_writer.indent_level += 1;

    let mut template_args = vec![];
    if let Some(mut imp) = item_impl {
        let (attrs, tmpl_vals) = extract_cpp_template_args(imp.attrs)?;
        if let Some(ty_args) = type_args {
            if let Some(span) = tmpl_vals.first().map(|t| t.span()).or_else(|| ty_args.keys().next().map(|i| i.span())) {
                if tmpl_vals.len() != ty_args.len() {
                    return Err(Error::new(span, "template argument mismatch".into()));
                }
                let targs = tmpl_vals.into_iter().zip(ty_args.keys()).collect::<Vec<_>>();
                template_args = targs;
            }
        }
        imp.attrs = attrs;
        item_impl = Some(imp);
    }

    let (passing_style, should_bind, needs_layout) = state.parse_zngur_meta_attributes(zng_writer, &zng_attrs, template_args)?;
    if needs_layout {
        if let Some(args) = type_args {
            zng_writer.layout(format!("{} < {} > ", item.ident, args.values().map(|ty| ty.to_token_stream().to_string()).collect::<Vec<_>>().join(", ")));
        } else {
            zng_writer.layout(item.ident.to_string());
        }
    }

    let mut bind_id = None;
    if let Some(imp) = item_impl {
        let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
        match state.mode {
            ParseMode::TypeCheck => {
                if should_bind {
                    for item in imp.items.iter() {
                        if let ImplItem::Fn(impl_fn) = item {
                            let (_, transfer_type) = extract_transfer_type_from_attributes(impl_fn.attrs.clone())?;
                            if transfer_type == Some(TransferType::Export) {
                                let span =     impl_fn.block.brace_token.span.span();
                                return Err(Error::new(span, "Syntax Error: bounded export functions cannot have a body".into()));
                            }
                        }
                    }
                }
            }
            ParseMode::Generate => {
                if should_bind {
                    let mut needs_trait = false;
                    for i in imp.items.iter() {
                        match i {
                            ImplItem::Fn(f) if matches!(f.sig.inputs.first(), Some(FnArg::Receiver(_))) => {
                                needs_trait = true;
                                break;
                            }
                            ImplItem::Verbatim(token_stream) => {
                                let (token_stream, transfer_type)  = extract_transfer_type_from_token_stream(token_stream.clone())?;
                                if matches!(transfer_type, Some(TransferType::Export)) {
                                    let token_stream = remove_semicolon(token_stream)?;
                                    let f: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                                    if matches!(f.sig.inputs.first(), Some(FnArg::Receiver(_))) {
                                        needs_trait = true;
                                        break;
                                    }
                                }
                            },
                            _ => continue,
                        }
                    }

                    if needs_trait {
                        let mut trait_fns = vec![];
                        imp.items.iter().map(|item| match item {
                            ImplItem::Fn(impl_fn) => {
                                let is_static = impl_fn.sig.inputs.first().map(|fst| !matches!(fst, FnArg::Receiver(..))).unwrap_or_default();
                                let (attrs, transfer_type) = extract_transfer_type_from_attributes(impl_fn.attrs.clone())?;
                                if !is_static && transfer_type == Some(TransferType::Export) {
                                    trait_fns.push(TraitItemFn {
                                        attrs,
                                        sig: impl_fn.sig.clone(),
                                        default: None,
                                        semi_token: None,
                                    });
                                }
                                Ok(())
                            }
                            ImplItem::Verbatim(token_stream) => {
                                let (token_stream, transfer_type)  = extract_transfer_type_from_token_stream(token_stream.clone()).unwrap();
                                if matches!(transfer_type, Some(TransferType::Export)) || matches!(transfer_type, None) {
                                    let token_stream = remove_semicolon(token_stream)?;
                                    let mut impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                                    let is_static = impl_fn.sig.inputs.first().map(|fst| !matches!(fst, FnArg::Receiver(..))).unwrap_or_default();

                                    impl_fn.sig.ident = Ident::new(&impl_fn.sig.ident.to_string().to_snake_case(), impl_fn.sig.ident.span());
                                    impl_fn.sig.inputs = impl_fn.sig.inputs.into_iter().map(|i| {
                                        match i {
                                            FnArg::Typed(mut pat_type) => {
                                                pat_type.pat = Box::new(match *pat_type.pat {
                                                    Pat::Ident(mut pat_id) => {
                                                        pat_id.ident =
                                                            Ident::new(&pat_id.ident.to_string().to_snake_case(), pat_id.ident.span());
                                                        Pat::Ident(pat_id)
                                                    }
                                                    pat => pat
                                                });
                                                FnArg::Typed(pat_type)
                                            }
                                            i => i,
                                        }
                                    }).collect();
                                    if !is_static {
                                        trait_fns.push(TraitItemFn {
                                            attrs: impl_fn.attrs,
                                            sig: to_guarded_signature(impl_fn.sig, state.mode),
                                            default: None,
                                            semi_token: None,
                                        });
                                    }
                                }
                                Ok(())
                            }
                            _ => Ok(())
                        }).collect::<Result<()>>()?;
                        let trait_id = Ident::new(&(item.ident.to_string() + "Trait"), Span::call_site());
                        let trait_: ItemTrait = parse_quote!{ pub trait #trait_id { #(#trait_fns)* } };
                        state.bind_traits.push(trait_);
                        bind_id = Some(trait_id);
                    }
                }
            }
        }

        for item in imp.items {
            state.parse_impl_item(zng_writer, Some(&imp.self_ty), item, trait_, false, lts)?;
        }
    }
    zng_writer.indent_level -= 1;
    zng_writer.wl("}".into());
    Ok((bind_id, passing_style))
}

#[cfg(not(feature = "mut-guard"))]
fn to_guarded_signature(sig: Signature, _mode: ParseMode) -> Signature { sig }

#[cfg(feature = "mut-guard")]
fn to_guarded_signature(mut sig: Signature, mode: ParseMode) -> Signature {
    if !matches!(mode, ParseMode::Generate) { return sig };

    fn to_guarded_type(ty: Type) -> Type {
        match ty {
            Type::Reference(ty_ref) if ty_ref.mutability.is_some() => {
                let is_prim = match &*ty_ref.elem {
                    Type::Path(TypePath { qself: None, path })
                        if path.is_ident("u32") || path.is_ident("i32") => true,
                    _ => false,
                };

                if is_prim {
                    Type::Reference(ty_ref)
                } else {
                    let ty = ty_ref.elem;
                    parse_quote!(GuardedMut<#ty>)
                }
            }
            Type::Path(TypePath { qself, mut path }) => {
                path.segments = path.segments.into_iter().map(|PathSegment { ident, arguments }| {
                    PathSegment {
                        ident,
                        arguments: match arguments {
                            PathArguments::None => PathArguments::None,
                            PathArguments::AngleBracketed(mut args) => {
                                args.args = args.args.into_iter().map(|arg| {
                                    match arg {
                                        GenericArgument::Type(ty) =>
                                            GenericArgument::Type(to_guarded_type(ty)),
                                        arg => arg
                                    }
                                }).collect();
                                PathArguments::AngleBracketed(args)
                            }
                            PathArguments::Parenthesized(mut args) => {
                                args.inputs = args.inputs.into_iter().map(to_guarded_type).collect();
                                args.output = match args.output {
                                    ReturnType::Type(rarrow, ty) =>
                                        ReturnType::Type(rarrow, Box::new(to_guarded_type(*ty))),
                                    x => x,
                                };
                                PathArguments::Parenthesized(args)
                            }
                        }
                    }
                }).collect();
                Type::Path(TypePath { qself, path })
            }
            ty => ty,
        }
    }


    sig.inputs = sig.inputs.into_iter().scan(false, |has_receiver, i| {
        match i {
            x @ FnArg::Receiver(_) => {
                *has_receiver = true;
                Some(x)
            },
            FnArg::Typed(mut pat_type) => {
                if *has_receiver {
                    pat_type.ty = Box::new(to_guarded_type(*pat_type.ty));
                }
                Some(FnArg::Typed(pat_type))
            }
        }
    }).collect();
    sig.output = match sig.output {
        ReturnType::Default => ReturnType::Default,
        ReturnType::Type(rarrow, ty) =>
            ReturnType::Type(rarrow, Box::new(to_guarded_type(*ty))),
    };
    sig
}
