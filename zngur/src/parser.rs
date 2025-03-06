use std::{borrow::Cow, cell::RefCell, collections::{hash_map::Entry, HashMap, HashSet}, rc::Rc};
use heck::ToSnakeCase;
use proc_macro2::{Span, TokenTree};
use quote::{ToTokens, TokenStreamExt};
use syn::{parse::Parse, parse_quote, punctuated::Punctuated, spanned::Spanned, AngleBracketedGenericArguments, Attribute, Block, Fields, FnArg, GenericArgument, GenericParam, Ident, ImplItem, ImplItemFn, Item, ItemConst, ItemEnum, ItemExternCrate, ItemFn, ItemForeignMod, ItemImpl, ItemMacro, ItemMod, ItemStatic, ItemStruct, ItemTrait, ItemTraitAlias, ItemType, ItemUnion, ItemUse, Lit, LitStr, Meta, MetaList, Pat, PatType, Path, PathArguments, PathSegment, ReturnType, Signature, Token, TraitItem, TraitItemFn, Type, TypeArray, TypeBareFn, TypeGroup, TypeParamBound, TypeParen, TypePath, TypePtr, TypeReference, TypeSlice, TypeTuple, Visibility};
use crate::instantiate::Instantiate;
use super::{Result, Error};

const META_TYPE_NAME: &'static str = "_Type";

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

fn impl_typename(self_ty: &Type) -> Result<String> {
    let span = self_ty.span();
    let syn::Type::Path(type_path) = &self_ty else { return Err(Error::new(span, "invalid type".into())); };
    for seg in &type_path.path.segments {
        let PathSegment { ident, arguments } = seg;
        match arguments {
            PathArguments::None => {
                return Ok(format!("{}", ident));
            },
            PathArguments::AngleBracketed(args) if ident == META_TYPE_NAME && args.args.len() == 1 => {
                let arg = args.args.first().unwrap();
                return Ok(format!("{}", arg.to_token_stream()))
            }
            PathArguments::AngleBracketed(..) => {
                return Ok(format!("{}", ident));
            }
            _ => continue
        }
    }
    Err(Error::new(span, "invalid argument".into()))
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
                                        match cpp::CppParser::parse(tokens) {
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

#[derive(Debug, Eq, Hash, PartialEq)]
struct Specialization {
    path: Vec<Ident>,
    args: Rc<Vec<Type>>,
    modpath: Rc<Vec<String>>,
}
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

#[derive(Debug, Eq, PartialEq)] 
pub enum ParseMode {
    TypeCheck,
    Generate,
}

pub struct Parser {
    n: usize,
    modstack: RefCell<Vec<(
        String,
        HashSet<String>,
        HashSet<String>,
    )>>,
    impls: HashMap<Vec<String>, ItemImpl>,
    structs_that_bind: HashMap<Ident, Path>,
    prelude_types: HashMap<Ident, Vec<Ident>>,
    cpp_writer: Option<CppWriter>,
    zng_writer: ZngWriter,
    specializations: HashMap<Ident, HashSet<Specialization>>,
    has_generated: bool,
    mode: ParseMode,
    bind_traits: Vec<ItemTrait>,
}
impl Parser {
    pub fn new(additional_includes: &Vec<String>, prelude_types: HashMap<Ident, Vec<Ident>>) -> Self {
        Self::with_details(false, additional_includes, prelude_types, false, ParseMode::Generate)
    }
    pub fn with_details(has_generated: bool, additional_includes: &Vec<String>, prelude_types: HashMap<Ident, Vec<Ident>>, skip_artifacts: bool, mode: ParseMode) -> Self {
        let mut ret = Self {
            has_generated,
            n: 0,
            modstack: RefCell::new(vec![]),
            impls: Default::default(),
            structs_that_bind: Default::default(),
            prelude_types,
            cpp_writer: None,
            zng_writer: ZngWriter::new(skip_artifacts),
            specializations: Default::default(),
            mode,
            bind_traits: vec![],
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
        let mut preludes = self.prelude_types.iter().filter_map(|(_, modpath)| {
            let mut mi = modpath.iter();
            match mi.next() {
                Some(f) => {
                    let rest = mi.map(|i| i.to_string()).collect::<Vec<_>>().join("::");
                    let first = if f == "std" { Cow::Borrowed("std_") } else { Cow::Owned(f.to_string()) };
                    if rest.is_empty() {
                        Some(format!("{}", first))
                    } else {
                        Some(format!("{}::{}", first, rest))
                    }
                }
                None => None,
            }
        }).collect::<Vec<_>>();
        preludes.sort();
        for p in preludes {
            writer.lines.push(format!("    using namespace {};", p));
        }
        self.cpp_writer = Some(writer);
    }
    pub fn take_cpp_writer(&mut self) -> Option<CppWriter> { self.cpp_writer.take() }
    pub fn map_type_paths(ty: Type, path_fn: &mut impl FnMut(Path) -> Path, lts: Option<&HashSet<&Ident>>) -> Type {
        match ty {
            Type::Array(TypeArray { bracket_token, elem, semi_token, len }) => 
                Type::Array(TypeArray { bracket_token, elem: Box::new(Self::map_type_paths(*elem, path_fn, lts)), semi_token, len }),
            Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token, inputs, variadic, output }) =>
                Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token,
                    inputs: inputs.into_iter().map(|mut i| { i.ty = Self::map_type_paths(i.ty, path_fn, lts); i }).collect(),
                    variadic, 
                    output: match output {
                        ReturnType::Type(rarrow, ty) => ReturnType::Type(rarrow, Box::new(Self::map_type_paths(*ty, path_fn, lts))),
                        x => x
                }
            }),
            Type::Group(TypeGroup { group_token, elem }) => 
                Type::Group(TypeGroup { group_token, elem: Box::new(Self::map_type_paths(*elem, path_fn, lts)) }),
            Type::Paren(TypeParen { paren_token, elem }) =>
                Type::Paren(TypeParen { paren_token, elem: Box::new(Self::map_type_paths(*elem, path_fn, lts)) }),
            Type::Path(TypePath { qself, path }) =>
                Type::Path(TypePath { qself, path: path_fn(path) }),
            Type::Ptr(TypePtr { star_token, const_token, mutability, elem }) =>
                Type::Ptr(TypePtr { star_token, const_token, mutability, elem: Box::new(Self::map_type_paths(*elem, path_fn, lts)) }),
            Type::Reference(TypeReference { and_token, lifetime, mutability, elem }) =>
                Type::Reference(TypeReference {
                    and_token,
                    lifetime: match (lts, lifetime) {
                        (Some(list), Some(lt)) => 
                            if list.contains(&lt.ident) { Some(lt) } else { None },
                        _ => None,
                    },
                    mutability,
                    elem: Box::new(Self::map_type_paths(*elem, path_fn, lts))
                }),
            Type::Slice(TypeSlice { bracket_token, elem }) =>
                Type::Slice(TypeSlice { bracket_token, elem: Box::new(Self::map_type_paths(*elem, path_fn, lts)) }),
            Type::Tuple(TypeTuple { paren_token, elems }) =>
                Type::Tuple(TypeTuple { paren_token, elems: elems.into_iter().map(|e| Self::map_type_paths(e, path_fn, lts)).collect() }),
            x => x
        }
    }
    fn fully_qualify_path(&self, mut p: Path, lts: Option<&HashSet<&Ident>>) -> Path {
        let is_std = p.segments.first().map(|s| s.ident == "std").unwrap_or_default();
        if is_std {
            p.leading_colon = Some(Token![::](p.span()));
            parse_quote!{ #p }
        } else {
            let modpath: Punctuated<_, Token![::]> = self.modpath().into_iter().map(|m| Ident::new(&m, p.span())).collect();
            let newpath: Path = parse_quote!{ #modpath::#p };
            let key = newpath.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>();
            if self.impls.get(&key).is_some() {
                p
            } else {
                let mut segments = p.segments.into_iter().collect::<Vec<_>>();
                if let Some(mut s) = segments.pop() {
                    s.arguments = match s.arguments {
                        PathArguments::AngleBracketed(mut args) => {
                            args.args = args.args.into_iter().filter_map(|a|
                                match a {
                                    GenericArgument::Type(ty) =>
                                        Some(GenericArgument::Type(
                                            Self::map_type_paths(ty, &mut |p| self.fully_qualify_path(p, lts), lts)
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
    fn collect_specialization(&mut self, type_path: TypePath, lts: Option<&HashSet<&Ident>>) -> TypePath {
        let TypePath { qself, path } = type_path;
        if let Some(seg) = path.segments.last() {
            if let PathArguments::AngleBracketed(args) = &seg.arguments {
                if let Some(path) = self.prelude_types.get(&seg.ident) {
                    let args = args.args.iter().filter_map(|a| match a {
                        GenericArgument::Type(ty) => {
                            Some(Self::map_type_paths(ty.clone(), &mut |p| self.fully_qualify_path(p, lts), lts))
                        },
                        _ => None,
                    }).collect::<Vec<_>>();
                    let s = Specialization {
                        path: path.clone(),
                        args: Rc::new(args),
                        modpath: Rc::new(self.modpath()),
                    };
                    match self.specializations.entry(seg.ident.clone()) {
                        Entry::Occupied(mut occupied_entry) => {
                            occupied_entry.get_mut().insert(s);
                        }
                        Entry::Vacant(vacant_entry) => {
                            let mut set = HashSet::new();
                            set.insert(s);
                            vacant_entry.insert(set);
                        }
                    }
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
            match &a.meta {
                Meta::Path(p) if p.is_ident("crate") => {
                    is_crate_mod = true;
                    false
                },
                _ => true
            }
        }).collect();
        if is_crate_mod {
            let mod_path = self.modstack.borrow().iter().skip(1).map(|(s, _, _)| s.as_str()).collect::<Vec<_>>().join(" :: ");
            (Some(format!("crate :: {mod_path}")), item_mod, true)
        } else {
            (Some(item_mod.ident.to_string()), item_mod, false)
        }
    }
    fn modpath(&self) -> Vec<String> {
        self.modstack.borrow().iter().skip(1).map(|(id, _, _)| id.clone()).collect::<Vec<_>>()
    }
    fn gensym(&mut self) -> proc_macro2::Ident {
        self.n += 1;
        proc_macro2::Ident::new(&format!("_{}", self.n), Span::call_site())
    }
    fn push_mod(&self, id: &Ident) {
        self.modstack.borrow_mut().push((id.to_string(), Default::default(), Default::default()));
    }
    fn pop_mod(&self) -> Vec<String> {
        if let Some((_, structs, impls)) = self.modstack.borrow_mut().pop() {
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
        if let Some((_, ref mut structs, _)) = self.modstack.borrow_mut().iter_mut().last() {
            structs.insert(id.to_string());
        }
    }
    fn declare_impl(&mut self, id: &Ident) {
        if let Some((_, _, ref mut impls)) = self.modstack.borrow_mut().iter_mut().last() {
            impls.insert(id.to_string());
        }
    }
    pub fn needed_layouts(&self) -> Vec<(Type, usize, usize)> {
        self.zng_writer.needed_layouts()
    }
    pub fn output(&mut self) -> Vec<String> {
        self.zng_writer.output()
    }
    fn collect_impls(&mut self, mut item_mod: ItemMod, on_should_bind: &mut impl FnMut(&Ident, &Path), on_impl: &mut impl FnMut(Vec<String>, ItemImpl)) -> Result<ItemMod> {
        self.push_mod(&item_mod.ident);
        item_mod.content = item_mod.content.map(|(b, items)| {
            let items: Vec<Item> = items.into_iter().map(|i| match i {
                Item::Mod(item_mod) => self.collect_impls(item_mod, on_should_bind, on_impl).map(Item::Mod),
                Item::Struct(item_struct) => {
                    if let Some(path) = get_bind_path(&item_struct.attrs) {
                        on_should_bind(&item_struct.ident, &path);
                    }
                    Ok(Item::Struct(item_struct))
                }
                Item::Impl(item_impl) if item_impl.trait_.is_none() => {
                    let mut modpath = self.modpath();
                    modpath.push(impl_typename(&*item_impl.self_ty)?);
                    on_impl(modpath, item_impl.clone());
                    Ok(Item::Impl(item_impl))
                }
                x => Ok(x)
            }).collect::<Result<Vec<_>>>()?;
            Result::<(syn::token::Brace, Vec<syn::Item>)>::Ok((b, items))
        }).transpose()?;
        let _ = self.pop_mod();
        Ok(item_mod)
    }
    pub fn parse(&mut self, item: ItemMod) -> Result<Vec<Item>> {
        let mut structs_that_bind = HashMap::<Ident, Path>::new();
        let mut impls = HashMap::<Vec<String>, ItemImpl>::new();
        let item = self.collect_impls(item,
            &mut|ident, path| {
                structs_that_bind.insert(ident.clone(), path.clone());
            },
            &mut |modpath, item_impl| {
                impls.insert(modpath, item_impl);
            }
        )?;
        self.impls = impls;
        self.structs_that_bind = structs_that_bind;

        let items = self.parse_mod(item)?.and_then(|item|
            item.content.map(|(_, items)| items)).unwrap_or_default();

        Ok(items)
    }
    fn parse_mod(&mut self, item: ItemMod) -> Result<Option<ItemMod>> {
        self.push_mod(&item.ident);
        let (mod_ident, item, is_crate) = self.parse_mod_ident(item);
        if let Some(ident) = &mod_ident {
            self.zng_writer.wl(format!("mod {} {{", ident).into());
            self.zng_writer.indent_level += 1;
        }
        let ItemMod { attrs, vis, unsafety, mod_token, ident, content, semi } = item;
        let content = content.map(|(b, items)|
            items.into_iter().map(|i|
                self.parse_item(i, is_crate))
                    .filter_map(|v| v.transpose())
                    .collect::<Result<_>>()
                    .map(|v: Vec<Item>| (b, v))
        ).transpose()?;
        if mod_ident.is_some() {
            self.zng_writer.indent_level -= 1;
            self.zng_writer.wl("}".into());
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
    fn parse_item(&mut self, item: Item, is_crate: bool) -> Result<Option<Item>> {
        Ok(match item {
            Item::Const(item_const) => self.parse_const(item_const)?.map(Item::Const),
            Item::Enum(item_enum) => self.parse_enum(item_enum, is_crate)?.map(Item::Enum),
            Item::ExternCrate(item_extern_crate) => self.parse_extern_crate(item_extern_crate)?.map(Item::ExternCrate),
            Item::Fn(item_fn) => self.parse_fn(item_fn)?.map(Item::Fn),
            Item::ForeignMod(item_foreign_mod) => self.parse_foreign_mod(item_foreign_mod)?.map(Item::ForeignMod),
            Item::Impl(item_impl) => {
                let has_imports = Self::has_imports(item_impl.items.iter())?;

                let disabled = self.zng_writer.disabled;
                self.zng_writer.disabled = true;
                let ret = self.parse_impl(item_impl.clone(), has_imports)?
                    .and_then(|imp| if imp.items.is_empty() { None } else { Some(Item::Impl(imp)) });
                self.zng_writer.disabled = disabled;

                if has_imports {
                    self.zng_writer.wl("extern \"C++\" {".into());
                    self.zng_writer.indent_level += 1;
                    let _ = self.parse_impl(item_impl, true)?;
                    self.zng_writer.indent_level -= 1;
                    self.zng_writer.wl("}".into());
                }
                ret
            },
            Item::Macro(item_macro) =>self.parse_macro(item_macro)?.map(Item::Macro),
            Item::Mod(item_mod) => self.parse_mod(item_mod)?.map(Item::Mod),
            Item::Static(item_static) => self.parse_static(item_static)?.map(Item::Static),
            Item::Struct(item_struct) => self.parse_struct(item_struct)?.map(Item::Struct),
            Item::Trait(item_trait) => self.parse_trait(item_trait)?.map(Item::Trait),
            Item::TraitAlias(item_trait_alias) => self.parse_trait_alias(item_trait_alias)?.map(Item::TraitAlias),
            Item::Type(item_type) =>  self.parse_type(item_type)?.map(Item::Type),
            Item::Union(item_union) => self.parse_union(item_union)?.map(Item::Union),
            Item::Use(item_use) => self.parse_use(item_use)?.map(Item::Use),
            Item::Verbatim(token_stream) => self.parse_verbatim(token_stream.clone())?.map(Item::Verbatim),
            x => {
                self.zng_writer.wl("// UNKNOWN".into());
                Some(x)
            },
        })
    }
    fn parse_const(&mut self, item: ItemConst) -> Result<Option<ItemConst>> {
        self.zng_writer.wl("CONST".into());
        Ok(Some(item))
    }
    fn parse_enum(&mut self, mut item_enum: ItemEnum, is_crate: bool) -> Result<Option<ItemEnum>> {
        let (attrs, transfer_type) = extract_transfer_type_from_attributes(item_enum.attrs)?;
        item_enum.attrs = attrs;

        if matches!(transfer_type, Some(TransferType::Expose)) || matches!(transfer_type, Some(TransferType::Export)) {
            let enum_modpath = {
                let mut modpath = self.modpath();
                modpath.push(item_enum.ident.to_string());
                modpath
            };
            let enum_impl = self.impls.remove(&enum_modpath);

            let num_generics = item_enum.generics.type_params().count();
            if num_generics == 0 {
                if is_crate {
                    item_enum.attrs.push(parse_quote! { #[repr(u32)] });
                    self.zng_writer.wl(format!("enum {} {{ {} }}", item_enum.ident, item_enum.variants.to_token_stream().to_string()).into());
                } else {
                    self.zng_writer.wl(format!("type {} {{", item_enum.ident).into());
                    self.zng_writer.indent_level += 1;
                    let is_std = enum_modpath.first().map(|s| s == "std").unwrap_or_default();
                    self.zng_writer.layout(if is_std {
                        format!(":: {}", enum_modpath.join(" :: "))
                    } else {
                        format!("{}", enum_modpath.join(" :: "))
                    });
                    for variant in item_enum.variants.iter() {
                        self.zng_writer.wl(format!("constructor {}{};", variant.ident, variant.fields.to_token_stream()).into());
                    }
                    if let Some(imp) = enum_impl {
                        let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
                        for item in imp.items {
                            self.parse_impl_item(Some(&item_enum.ident), item, trait_, false, None)?;
                        }
                    }
                    self.zng_writer.indent_level -= 1;
                    self.zng_writer.wl("}".into());
                }
            } else {
                let mut instantiated_items = vec![];
                if let Some(specializations) = self.specializations.get(&item_enum.ident) {
                    let mut specializations = specializations.iter().collect::<Vec<_>>();
                    specializations.sort();
                    for s in specializations.iter() {
                        let params = item_enum.generics.params.iter().filter_map(|p| match p {
                            GenericParam::Type(type_param) => Some(&type_param.ident),
                            _ => None
                        }).collect::<Vec<_>>();
                        if !s.args.is_empty() && params.len() != s.args.len() {
                            return Err(Error::new(item_enum.span(), "invalid number of generic arguments".into()));
                        }

                        let env = params.into_iter().zip(s.args.iter()).collect::<HashMap<_, _>>();
                        let inst = Instantiate::new(&*s.modpath, &env);
                        if let Some(item) = inst.item_enum(&item_enum) {
                            let enum_impl = enum_impl.as_ref().map(|i| inst.item_impl(i)).transpose()?;
                            instantiated_items.push((item, enum_impl, s.modpath.clone(), s.args.clone()));
                        }
                    }
                }

                for (item, enum_impl, modpath, args) in instantiated_items {
                    let mp: Punctuated::<_, Token![::]> = modpath.iter().map(|s| Ident::new(&s, item.span())).collect();
                    self.zng_writer.wl(format!("type {} < {} > {{", item.ident, args.iter().map(|a| {
                        let a = Self::map_type_paths(a.clone(), &mut |p| {
                            if p.leading_colon.is_some() { p } else {
                                parse_quote!(crate::#mp::#p)
                            }
                        }, None);
                        a.to_token_stream().to_string()
                    }).collect::<Vec<_>>().join(", ")).into());
                    self.zng_writer.indent_level += 1;
                    self.zng_writer.layout(format!("{} < {} > ", item.ident, args.iter().map(|a| a.to_token_stream().to_string()).collect::<Vec<_>>().join(", ")));
                    for variant in item.variants.iter() {
                        self.zng_writer.wl(format!("constructor {}{};", variant.ident, variant.fields.to_token_stream()).into());
                    }
                    if let Some(imp) = enum_impl {
                        let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
                        for item in imp.items {
                            let enum_ident = item_enum.ident.clone();
                            self.parse_impl_item(Some(&enum_ident), item, trait_, false, None)?;
                        }
                    }
                    self.zng_writer.indent_level -= 1;
                    self.zng_writer.wl("}".into());
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
    fn parse_extern_crate(&mut self, item: ItemExternCrate) -> Result<Option<ItemExternCrate>> {
        self.zng_writer.wl("EXTERN_CRATE".into());
        Ok(Some(item))
    }
    fn parse_fn(&mut self, item: ItemFn) -> Result<Option<ItemFn>> {
        Ok(Some(item))
    }
    fn parse_foreign_mod(&mut self, item: ItemForeignMod) -> Result<Option<ItemForeignMod>> {
        self.zng_writer.wl("FOREIGN_MOD".into());
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
    fn parse_impl(&mut self, item: ItemImpl, is_extern_cpp: bool) -> Result<Option<ItemImpl>> {
        let ItemImpl { attrs, defaultness, unsafety, impl_token, generics, trait_, self_ty, brace_token, items } = item;
        if let Some(attr) = attrs.first() {
            return Err(Error::new(attr.span(), "unexpected attribute".into()));
        }
        self.zng_writer.w("impl".into());
        let lifetimes = generics.lifetimes().collect::<Punctuated<_, Token![,]>>();
        if !lifetimes.is_empty() {
            self.zng_writer.w(format!("<{}>", lifetimes.to_token_stream()).into());
        }
        self.zng_writer.w(format!(" ").into());
        let lts = generics.lifetimes().map(|l| &l.lifetime.ident).collect::<HashSet<_>>();
        let (items, corrected_trait_) = if let Some((_, path, ..)) = &trait_ {
            let mut path = self.fully_qualify_path(path.clone(), Some(&lts));
            self.zng_writer.w(format!("{}", path.to_token_stream()).into());
            // Special case: In zngur, the `Iterator` trait's `Item` type is not defined as an associated type.
            // To handle this, we remove any `ImplItem::Type` with the identifier `Item` and re-insert it 
            // as a generic parameter instead. This preserves compatibility.
            let items = if let Some(last) = path.segments.last_mut() {
                let items = items.into_iter().map(|i| match i {
                    ImplItem::Type(i) if i.ident == "Item" => {
                        self.zng_writer.w(format!("<Item = {}>", i.ty.to_token_stream()).into());
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
            self.zng_writer.w(" for ".into());
            (items, Some(path))
        } else { (items, None) };
        let span = self_ty.span();
        let mut self_ident = None;
        let syn::Type::Path(mut type_path) = *self_ty else { return Err(Error::new(span, "invalid type".into())); };
        type_path.path.segments = type_path.path.segments.into_iter().map(|seg| {
            let PathSegment { ident, arguments } = seg;
            let (ident, arguments) = match arguments {
                PathArguments::None => {
                    self.zng_writer.w(format!("{}", ident).into());
                    self_ident = Some(ident.clone());
                    Ok((ident, PathArguments::None))
                },
                PathArguments::AngleBracketed(args) if ident == META_TYPE_NAME && args.args.len() == 1 => {
                    let arg = args.args.first().unwrap();
                    self.zng_writer.w(format!("{}", arg.to_token_stream()).into());
                    Ok((self.gensym(), PathArguments::None))
                }
                PathArguments::AngleBracketed(args) => {
                    self.zng_writer.w(format!("{}<{}>", ident, args.args.to_token_stream()).into());
                    self_ident = Some(ident.clone());
                    Ok((ident, PathArguments::AngleBracketed(args)))
                }
                x => Err(Error::new(x.span(), "invalid argument".into()))
            }?;
            self.declare_impl(&ident);
            Ok(PathSegment { ident, arguments })
        }).collect::<Result<_>>()?;

        self.zng_writer.wl(" {".into());
        self.zng_writer.indent_level += 1;
        let items: Vec<ImplItem> = items.into_iter()
            .filter_map(|item| {
                self.parse_impl_item(self_ident.as_ref(), item, corrected_trait_.as_ref(), is_extern_cpp, Some(&lts)).transpose()
            }).collect::<Result<_>>()?;
        self.zng_writer.indent_level -= 1;
        self.zng_writer.wl("}".into());
        let self_ty = Box::new(syn::Type::Path(type_path));
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
    fn parse_macro(&mut self, item: ItemMacro) -> Result<Option<ItemMacro>> {
        self.zng_writer.wl("MACRO".into());
        Ok(Some(item))
    }
    fn parse_static(&mut self, item: ItemStatic) -> Result<Option<ItemStatic>> {
        self.zng_writer.wl("STATIC".into());
        Ok(Some(item))
    }
    fn parse_meta_attributes(&mut self, ty_str: String, attrs: Vec<Attribute>) -> Result<(Vec<Attribute>, Option<CppPassingStyle>, bool)> {
        let mut needs_layout = true;
        let mut passing_style = None;
        let mut should_bind = false;
        let ret = attrs.into_iter().map(|attr| Ok({
            let Attribute { pound_token, style, bracket_token, meta } = attr;
            let meta = match meta {
                Meta::List(meta_list) if meta_list.path.is_ident("bind_to") => {
                    should_bind = true;
                    None
                }
                Meta::List(mut meta_list) if meta_list.path.is_ident("wellknown") => {
                    meta_list.path = proc_macro2::Ident::new("derive", meta_list.path.span()).into();
                    let tokens = meta_list.tokens.to_token_stream().into_iter().collect::<Vec<_>>();
                    let mut found_index = None;
                    tokens.windows(2).enumerate().for_each(|(n, toks)| {
                        match (&toks[0], &toks[1]) {
                            (TokenTree::Punct(a), TokenTree::Ident(b)) if a.as_char() == '?' && b == "Sized" => {
                                found_index = Some(n);
                                self.zng_writer.wl(format!("wellknown_traits(?Sized);").into());
                                needs_layout = false;
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
                                    self.zng_writer.wl(format!("wellknown_traits(Copy);").into());
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
                    Some(Meta::List(meta_list))
                }
                Meta::List(meta_list) if meta_list.path.is_ident("cpp_value") => {
                    self.zng_writer.wl("constructor(ZngurCppOpaqueOwnedObject);".into());
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid cpp_value token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Int(a)), Some(Lit::Str(b)), None) = (ai.next(), ai.next(), ai.next()) else {
                        return Err(Error::new(span, "invalid cpp_value token".into()))
                    }; 
                    self.zng_writer.wl(format!("#cpp_value \"{}\" \"{}\";", a.base10_digits(), b.value()).into());
                    passing_style = Some(CppPassingStyle::Value);
                    None
                }
                Meta::List(meta_list) if meta_list.path.is_ident("rust_value") => {
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid rust_value token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Int(a)), Some(Lit::Str(b)), None) = (ai.next(), ai.next(), ai.next()) else {
                        return Err(Error::new(span, "invalid rust_value token".into()))
                    }; 
                    self.zng_writer.wl(format!("#rust_value \"{}\" \"{}\";", a.base10_digits(), b.value()).into());
                    None
                }
                Meta::List(meta_list) if meta_list.path.is_ident("cpp_ref") => {
                    let span = meta_list.span();
                    let Ok(args) = meta_list.parse_args_with(
                        Punctuated::<Lit, syn::Token![,]>::parse_terminated) else {
                        return Err(Error::new(span, format!("invalid cpp_ref token list").into()));
                    };
                    let mut ai = args.into_iter();
                    let (Some(Lit::Str(a)), None) = (ai.next(), ai.next()) else {
                        return Err(Error::new(span, format!("invalid cpp_ref token").into()));
                    };
                    self.zng_writer.wl(format!("#cpp_ref \"{}\";", a.value()).into());
                    needs_layout = false;
                    passing_style = Some(CppPassingStyle::Ref);
                    None
                }
                x => Some(x),
            };
            meta.map(|meta| Attribute { pound_token, style, bracket_token, meta })
        })).filter_map(|a| a.transpose()).collect::<Result<_>>()?;
        if needs_layout {
            self.zng_writer.layout(ty_str);
        }
        Ok((ret, passing_style, should_bind))
    }

    fn parse_struct(&mut self, item: ItemStruct) -> Result<Option<ItemStruct>> {
        let ItemStruct { attrs, vis, struct_token, ident, generics, fields, semi_token } = item;
        let mut bind_id = None;
        let mut modpath = self.modpath();
        let (attrs, ident, passing_style, is_meta_type) = if ident == META_TYPE_NAME {
            let span = fields.span();
            let (1, Some(syn::Field { ident: None, ty , .. })) = (fields.len(), fields.iter().next()) else { return Err(Error::new(span, "expects a single field".into())); };
            let ty = Self::map_type_paths(ty.clone(), &mut |p| self.fully_qualify_path(p, None), None);
            modpath.push(ty.to_token_stream().to_string());
            self.zng_writer.wl(format!("type {} {{", ty.to_token_stream()).into());
            self.zng_writer.indent_level += 1;
            let (attrs, passing_style, _) = self.parse_meta_attributes(ty.to_token_stream().to_string(), attrs)?;
            if let Some(imp) = self.impls.remove(&modpath) {
                let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
                for item in imp.items {
                    self.parse_impl_item(Some(&ident), item, trait_, false, None)?;
                }
            }
            self.zng_writer.indent_level -= 1;
            self.zng_writer.wl("}".into());
            (attrs, self.gensym(), passing_style, self.mode != ParseMode::TypeCheck)
        } else {
            modpath.push(ident.to_token_stream().to_string());
            self.zng_writer.wl(format!("type {} {{", ident.to_token_stream()).into());
            self.zng_writer.indent_level += 1;
            let (attrs, passing_style, should_bind) = self.parse_meta_attributes(ident.to_string(), attrs)?;
            if let Some(imp) = self.impls.remove(&modpath) {
                let trait_ = imp.trait_.as_ref().map(|tr| &tr.1);
                match self.mode {
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
                                                semi_token,
                                            });
                                        }
                                        Ok(())
                                    }
                                    ImplItem::Verbatim(token_stream) => {
                                        let (token_stream, transfer_type)  = extract_transfer_type_from_token_stream(token_stream.clone()).unwrap();
                                        if matches!(transfer_type, Some(TransferType::Export)) {
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
                                                    sig: impl_fn.sig.clone(),
                                                    default: None,
                                                    semi_token,
                                                });
                                            }
                                        }
                                        Ok(())
                                    }
                                    _ => Ok(())
                                }).collect::<Result<_>>()?;
                                let trait_id = Ident::new(&(ident.to_string() + "Trait"), Span::call_site());
                                let trait_: ItemTrait = parse_quote!{ pub trait #trait_id<'a> { #(#trait_fns)* } };
                                self.bind_traits.push(trait_);
                                bind_id = Some(trait_id);
                            }
                        }
                    }
                }

                for item in imp.items {
                    self.parse_impl_item(Some(&ident), item, trait_, false, None)?;
                }
            }
            self.zng_writer.indent_level -= 1;
            self.zng_writer.wl("}".into());
            (attrs, ident, passing_style, false)
        };
        self.declare_type_identifier(&ident);
        if let Some(trait_ident) = bind_id {
            Ok(Some(parse_quote! {
                #vis struct #ident<'a>(Box<dyn #trait_ident<'a> + 'a>);
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
    fn parse_trait(&mut self, item: ItemTrait) -> Result<Option<ItemTrait>> {
        self.zng_writer.wl("TRAIT".into());
        Ok(Some(item))
    }
    fn parse_trait_alias(&mut self, item: ItemTraitAlias) -> Result<Option<ItemTraitAlias>> {
        self.zng_writer.wl("TRAIT_ALIAS".into());
        Ok(Some(item))
    }
    fn parse_type(&mut self, item: ItemType) -> Result<Option<ItemType>> {
        self.zng_writer.wl("TYPE".into());
        Ok(Some(item))
    }
    fn parse_union(&mut self, item: ItemUnion) -> Result<Option<ItemUnion>> {
        self.zng_writer.wl("UNION".into());
        Ok(Some(item))
    }
    fn parse_use(&mut self, item: ItemUse) -> Result<Option<ItemUse>> {
        Ok(Some(item))
    }
    fn parse_verbatim(&mut self, token_stream: proc_macro2::TokenStream) -> Result<Option<proc_macro2::TokenStream>> {
        let (token_stream, transfer_type) = extract_transfer_type_from_token_stream(token_stream.clone())?;
        match transfer_type {
            Some(TransferType::Expose) => {
                let token_stream = remove_semicolon(token_stream)?;
                let item_fn: ItemFn = parse_quote! { #token_stream { unimplemented!() } };
                self.parse_sig(None, item_fn.sig, None)?;
                Ok(None)
            }
            Some(TransferType::Export) => {
                Ok(Some(token_stream))
            }
            Some(TransferType::Import(cpp_lines)) => {
                self.zng_writer.wl("extern \"C++\" {".into());
                self.zng_writer.indent_level += 1;
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
                item_fn.sig = self.parse_sig(None, item_fn.sig, None)?;
                self.zng_writer.indent_level -= 1;
                self.zng_writer.wl("}".into());
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
    fn parse_ty(&mut self, ty: syn::Type, lts: Option<&HashSet<&Ident>>) -> Result<syn::Type> {
        Ok(match ty {
            syn::Type::Array(type_array) => {
                self.zng_writer.wl("[ARRAY]".into());
                syn::Type::Array(type_array)
            }
            syn::Type::BareFn(type_bare_fn) => {
                self.zng_writer.wl("[BARE_FN]".into());
                syn::Type::BareFn(type_bare_fn)
            }
            syn::Type::Group(type_group) => {
                self.zng_writer.wl("//[GROUP]".into());
                syn::Type::Group(type_group)
            }
            syn::Type::ImplTrait(type_impl_trait) => {
                self.zng_writer.wl("//[IMPL_TRAIT]".into());
                syn::Type::ImplTrait(type_impl_trait)
            }
            syn::Type::Infer(type_infer) => {
                self.zng_writer.wl("//[INFER]".into());
                syn::Type::Infer(type_infer)
            }
            syn::Type::Macro(type_macro) => {
                self.zng_writer.wl("//[MACRO]".into());
                syn::Type::Macro(type_macro)
            }
            syn::Type::Never(type_never) => {
                self.zng_writer.wl("//[NEVER]".into());
                syn::Type::Never(type_never)
            }
            syn::Type::Paren(type_paren) => {
                self.zng_writer.wl("//[PAREN]".into());
                syn::Type::Paren(type_paren)
            }
            syn::Type::Path(type_path) => {
                let type_path = self.collect_specialization(type_path, lts);
                //self.wl("//[PATH]");
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
                self.zng_writer.wl("//[SLICE]".into());
                syn::Type::Slice(type_slice)
            }
            syn::Type::TraitObject(type_trait_object) => {
                self.zng_writer.wl("//[TRAIT_OBJECT]".into());
                syn::Type::TraitObject(type_trait_object)
            }
            syn::Type::Tuple(type_tuple) => {
                syn::Type::Tuple(type_tuple)
            }
            syn::Type::Verbatim(token_stream) => {
                self.zng_writer.wl("//[TOKEN_STREAM]".into());
                syn::Type::Verbatim(token_stream)
            }
            ty => ty
        })
    }
    fn parse_impl_item(&mut self, self_ident: Option<&Ident>, item: ImplItem, trait_: Option<&Path>, is_extern_cpp: bool, lts: Option<&HashSet<&Ident>>) -> Result<Option<ImplItem>> {
        match item {
            ImplItem::Const(impl_item_const) => {
                self.zng_writer.wl("// (CONST)".into());
                Ok(Some(syn::ImplItem::Const(impl_item_const)))
            }
            ImplItem::Fn(impl_item_fn) => {
                let ImplItemFn { attrs, vis, defaultness, mut sig, block } = impl_item_fn;
                let (attrs, transfer_type) = extract_transfer_type_from_attributes(attrs)?;
                if transfer_type.as_ref().map(|t| matches!(t, TransferType::Import(..))).unwrap_or_default() {
                    Err(Error::new(block.span(), "imports cannot have an implementation".into()))
                } else if transfer_type == Some(TransferType::Export) {
                    let prev_disabled = if !is_extern_cpp { None } else { Some(self.zng_writer.disabled) };
                    if prev_disabled.is_some() { self.zng_writer.disabled = true; }
                    sig = self.parse_sig(self_ident, sig, lts)?;
                    prev_disabled.map(|d| self.zng_writer.disabled = d);

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
                    if self.mode == ParseMode::Generate && should_bind {
                        panic!("{:?}", sig.ident);
                    }
                    let impl_item_fn = ImplItemFn { attrs, vis, defaultness, sig, block };
                    Ok(Some(ImplItem::Fn(impl_item_fn)))
                }
            }
            ImplItem::Type(impl_item_type) => {
                Ok(Some(syn::ImplItem::Type(impl_item_type)))
            }
            ImplItem::Macro(impl_item_macro) => {
                self.zng_writer.wl("// (MACRO)".into());
                Ok(Some(syn::ImplItem::Macro(impl_item_macro)))
            }
            ImplItem::Verbatim(token_stream) => {
                let (token_stream, transfer_type) = extract_transfer_type_from_token_stream(token_stream)?;
                match transfer_type {
                    Some(TransferType::Expose) => {
                        let token_stream = remove_semicolon(token_stream)?;
                        let impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!() } };
                        self.parse_sig(self_ident, impl_fn.sig, lts)?;
                        Ok(None)
                    }
                    Some(TransferType::Export) => {
                        let should_bind = self_ident.map(|id| self.structs_that_bind.contains_key(id)).unwrap_or_default();
                        if should_bind {
                            let token_stream = remove_semicolon(token_stream)?;
                            let mut impl_fn: ImplItemFn = parse_quote! { #token_stream { unimplemented!("D") } };
                            impl_fn.attrs.push(parse_quote! { #[export] });
                            self.parse_impl_item(self_ident, ImplItem::Fn(impl_fn), trait_, is_extern_cpp, lts)
                        } else {
                            Ok(Some(ImplItem::Verbatim(token_stream)))
                        }
                    }
                    Some(TransferType::Import(cpp_lines)) => {
                        let token_stream = remove_semicolon(token_stream)?;
                        let ImplItemFn { attrs, vis, defaultness, mut sig, block } = parse_quote! { #token_stream { unimplemented!() } };
                        let modpath = self.modpath();
                        if let Some((lines, w)) = cpp_lines.zip(self.cpp_writer.as_mut()) {
                            w.add_lines(modpath, self_ident, trait_, &sig, &lines);
                        }
                        if is_extern_cpp {
                            sig = self.parse_sig(self_ident, sig, lts)?;
                        }
                        if self.has_generated || self.mode == ParseMode::Generate {
                            Ok(None)
                        } else {
                            Ok(Some(ImplItem::Fn(ImplItemFn { attrs, vis, defaultness, sig, block })))
                        }
                    }
                    None => {
                        Ok(Some(ImplItem::Verbatim(token_stream)))
                    }
                }
            }
            x => {
                self.zng_writer.wl("// (UNKNOWN)".into());
                Ok(Some(x))
            }
        }
    }
    fn parse_sig(&mut self, self_ident: Option<&Ident>, sig: Signature, lts: Option<&HashSet<&Ident>>) -> Result<Signature> {
        let inputs = sig.inputs.iter().map(|i| Ok(match i {
            FnArg::Receiver(receiver) => receiver.to_token_stream(),
            FnArg::Typed(pat_type) => {
                let ty = self.parse_ty(*pat_type.ty.clone(), lts)?;
                Self::map_type_paths(ty, &mut |p| self.fully_qualify_path(p, lts), lts).to_token_stream()
            },
        })).collect::<Result<Punctuated<_, Token![,]>>>()?;
        self.zng_writer.w(format!("fn {}({})", sig.ident, inputs.to_token_stream()).into());
        if let ReturnType::Type(_, ty) = &sig.output {
            let ty = self.parse_ty(*ty.clone(), lts)?;
            self.zng_writer.w(match (ty, self_ident) {
                (Type::Path(TypePath { path, .. }), Some(ident)) if path.is_ident("Self") =>
                    format!(" -> {}", ident.to_token_stream()).into(),
                (ty, _) => {
                    let ty = Self::map_type_paths(ty, &mut |p| self.fully_qualify_path(p, lts), lts);
                    format!(" -> {}", ty.to_token_stream()).into()
                }
            });
        }
        self.zng_writer.wl(";".into());
        Ok(sig)
    }
}

pub struct CppWriter {
    lines: Vec<String>,
    dupcheck: HashSet<(Option<Ident>, Ident)>,
}
impl CppWriter {
    pub fn new() -> Self {
        let mut ret = Self {
            lines: vec![],
            dupcheck: Default::default(),
        };
        ret.lines.append(&mut [
            "namespace rust {",
            "    using namespace crate;"
        ].into_iter().map(|s| s.to_string()).collect());
        ret
    }
    fn add_line(&mut self, modpath: Vec<String>, self_ident: Option<&Ident>, trait_: Option<&Path>, sig: &Signature, line: impl ToString) {
        let key = (self_ident.cloned(), sig.ident.clone());
        if self.dupcheck.contains(&key) { return };
        self.dupcheck.insert(key);

        let cpp_sig = Self::cpp_sig(&modpath.join("::"), self_ident, trait_, sig);
        self.lines.push(format!("{}", cpp_sig));

        self.lines.push(line.to_string());
        self.lines.push("}".to_string());
    }
    pub fn add_lines(&mut self, modpath: Vec<String>, self_ident: Option<&Ident>, trait_: Option<&Path>, sig: &Signature, lines: &[impl ToString]) {
        let key = (self_ident.cloned(), sig.ident.clone());
        if self.dupcheck.contains(&key) { return };
        self.dupcheck.insert(key);

        let cpp_sig = Self::cpp_sig(&modpath.join("::"), self_ident, trait_, sig);
        self.lines.push(format!("{}", cpp_sig));

        self.lines.append(&mut lines.into_iter().map(|c| c.to_string()).collect());
        self.lines.push("}".to_string());
    }
    pub fn output(mut self) -> String {
        self.lines.append(&mut [
            "}",
            //"// NOTE: when return RefMut/Ref, matching std::ref/std::cref must be used",
        ].into_iter().map(|s| s.to_string()).collect());
        self.lines.join("\n")
    }
    fn cpp_sig(modpath: &String, self_ident: Option<&Ident>, trait_: Option<&Path>, sig: &Signature) -> String {
        struct Cpp<'a> { modpath: &'a String, self_ident: Option<&'a Ident> }
        impl<'a> Cpp<'a> {
            fn ident(&self, i: &Ident) -> String {
                match i {
                    i if i == "i8" => "::int8_t".to_string(),
                    i if i == "i16" => "::int16_t".to_string(),
                    i if i == "i32" => "::int32_t".to_string(),
                    i if i == "i64" => "::int64_t".to_string(),
                    i if i == "u8" => "::uint8_t".to_string(),
                    i if i == "u16" => "::uint16_t".to_string(),
                    i if i == "u32" => "::uint32_t".to_string(),
                    i if i == "u64" => "::uint64_t".to_string(),
                    i if i == "f32" => "float".to_string(),
                    i if i == "f64" => "double".to_string(),
                    i if i == "bool" => "Bool".to_string(),
                    i if i == "str" => "Str".to_string(),
                    i if self.modpath.is_empty() => i.to_string(),
                    i => format!("{}::{}", self.modpath, i),
                }
            }
            fn path_segment(&self, s: &PathSegment) -> String {
                let args = match &s.arguments {
                    PathArguments::None => "".to_string(),
                    PathArguments::AngleBracketed(a) =>
                        a.args.iter().map(|a| match a {
                            GenericArgument::Lifetime(lifetime) => "TYARGS[1]".to_string(),
                            GenericArgument::Type(ty) => format!("{}", self.ty(ty)),
                            GenericArgument::Const(expr) => "TYARGS[3]".to_string(),
                            GenericArgument::AssocType(assoc_type) => "TYARGS[4]".to_string(),
                            GenericArgument::AssocConst(assoc_const) => "TYARGS[5]".to_string(),
                            GenericArgument::Constraint(constraint) => "TYARGS[6]".to_string(),
                            _ => "TYARGS[??]".to_string(),
                        }).collect::<Vec<_>>().join(", "),
                    PathArguments::Parenthesized(a) => {
                        let mut tys = a.inputs.iter().map(|i| self.ty(i)).collect::<Vec<_>>();
                        tys.push(match &a.output {
                            ReturnType::Default => "Unit".to_string(),
                            ReturnType::Type(_, ty) => self.ty(&*ty),
                        });
                        format!("{}", tys.join(", "))
                    }
                };
                if args.is_empty() {
                    format!("{}", s.ident)
                } else {
                    format!("{}<{}>", s.ident, args)
                }
            }
            fn path(&self, p: &Path) -> String {
                match p.get_ident() {
                    Some(i) => self.ident(i),
                    None => {
                        let mut si = p.segments.iter();
                        match (si.next(), si.next()) {
                            (Some(a), None) => self.path_segment(a),
                            (Some(a), Some(b)) if a.ident == "std" => {
                                let rest = si.map(|s| self.path_segment(s)).collect::<Vec<_>>();
                                if rest.is_empty() {
                                    format!("std_::{}", self.path_segment(b))
                                } else {
                                    format!("std_::{}::{}", self.path_segment(b), rest.join("::"))
                                }
                            }
                            _ => format!("TY_9[{}]", p.to_token_stream())
                        }

                    }
                }
            }
            fn ty(&self, ty: &Type) -> String {
                match ty {
                    Type::Array(t) => format!("TY1[{}]", t.to_token_stream()),
                    Type::BareFn(t) => format!("TY2[{}]", t.to_token_stream()),
                    Type::Group(t) => format!("TY3[{}]", t.to_token_stream()),
                    Type::ImplTrait(t) => format!("TY4[{}]", t.to_token_stream()),
                    Type::Infer(t) => format!("TY5[{}]", t.to_token_stream()),
                    Type::Macro(t) => format!("TY6[{}]", t.to_token_stream()),
                    Type::Never(t) => format!("TY7[{}]", t.to_token_stream()),
                    Type::Paren(t) => format!("TY8[{}]", t.to_token_stream()),
                    Type::Path(t) if t.path.is_ident("Self") && self.self_ident.is_some() => self.ident(self.self_ident.unwrap()),
                    Type::Path(t) => self.path(&t.path),
                    Type::Ptr(t) => format!("TY10[{}]", t.to_token_stream()),
                    Type::Reference(t) => format!("{}<{}>", if t.mutability.is_some() { "RefMut" } else { "Ref" }, self.ty(&*t.elem)),
                    Type::Slice(t) => format!("Slice<{}>", self.ty(&*t.elem)),
                    Type::TraitObject(t) => {
                        let bounds = t.bounds.iter().map(|b| match b {
                            TypeParamBound::Trait(trait_bound) => self.path(&trait_bound.path),
                            TypeParamBound::Lifetime(l) => "BOUND2".to_string(),
                            TypeParamBound::PreciseCapture(pc) => "BOUND3".to_string(),
                            TypeParamBound::Verbatim(ts) => "BOUND4".to_string(),
                            _ => "BOUND[??]".to_string(),
                        }).collect::<Vec<_>>().join(" + ");
                        format!("Dyn<{}>", bounds)
                    },
                    Type::Tuple(t) => format!("Tuple<{}>", t.elems.iter().map(|e| self.ty(e)).collect::<Vec<_>>().join(", ")),
                    Type::Verbatim(t) => format!("TY15[{}]", t.to_token_stream()),
                    _ => "???".to_string(),
                }
            }
        }

        let cpp = Cpp { modpath, self_ident };

        let output = match &sig.output {
            ReturnType::Default => "void".to_string(),
            ReturnType::Type(_, ty) => cpp.ty(&*ty),
        };

        let inputs = sig.inputs.iter().map(|i| {
            match i {
                FnArg::Receiver(r) => {
                    let ty = cpp.ty(&*r.ty);
                    format!("{} {}", ty, r.self_token.to_token_stream())
                }
                FnArg::Typed(pat_type) => {
                    let ty = cpp.ty(&*pat_type.ty);
                    format!("{} {}", ty, pat_type.pat.to_token_stream())
                }
            }
        }).collect::<Vec<_>>().join(", ");

        let sig_ident = match &sig.ident {
            i if i == "new" => Cow::Borrowed("new_"),
            _ => Cow::Owned(sig.ident.to_string()),
        };

        if let Some(ident) = self_ident {
            let tr = trait_.map(|p| Cow::Owned(cpp.path(p))).unwrap_or(Cow::Borrowed("Inherent"));
            if modpath.is_empty() {
                format!("{} Impl<{}, {}>::{}({}) {{", output, ident, tr, sig_ident, inputs)
            } else {
                format!("{} Impl<{}::{}, {}>::{}({}) {{", output, modpath, ident, tr, sig_ident, inputs)
            }
        } else {
            format!("{} exported_functions::{}({}) {{", output, sig_ident, inputs)
        }
    }
}

mod cpp {
    use crate::{Result, Error};
    use proc_macro2::{Delimiter, TokenStream, TokenTree};

    enum Expr {
        Literal(String),
        Variable(String),
        Binary { left: Box<Expr>, op: String, right: Box<Expr> },
        Call { func: String, args: Vec<Expr> },
        Member { base: Box<Expr>, member: String },
    }

    enum Stmt {
        HashIf(String),
        HashElse,
        HashEndIf,
        VarDecl { ty: String, name: String, init: Option<Expr> },
        Expr(Expr),
        Return(Expr),
        If { cond: Expr, then_branch: Block, else_branch: Option<Block> },
        While { cond: Expr, body: Block },
        For { init: Box<Stmt>, cond: Expr, step: Expr, body: Block },
    }

    struct Block {
        stmts: Vec<Stmt>,
    }


    pub struct CppParser;
    impl CppParser {
        pub fn parse(ts: TokenStream) -> Result<String> {
            println!("PARSE: {:#?}", ts);
            let mut stmts = vec![];
            let mut ti = ts.into_iter();
            while let Some(t) = ti.next() {
                let s = Self::parse_token_tree(t)?;
                stmts.push(s);
            }
            let ret = stmts.join("");
            println!("CPP[\n{}\n]", ret);
            Ok(ret)
        }
        fn parse_token_stream(ts: TokenStream) -> Result<Vec<String>> {
            ts.into_iter().map(|t| Self::parse_token_tree(t)).collect::<Result<_>>()
        }
        fn parse_token_tree(t: TokenTree) -> Result<String> {
            Ok(match t {
                TokenTree::Group(group) => {
                    match group.delimiter() {
                        Delimiter::Parenthesis => {
                            let vals = Self::parse_token_stream(group.stream())?.join("");
                            format!("({})", vals)
                        }
                        Delimiter::Brace => {
                            let vals = Self::parse_stmts(group.stream())?.join("");
                            format!(" {{\n{}}} ", vals)
                        }
                        Delimiter::Bracket => {
                            let vals = Self::parse_token_stream(group.stream())?.join("");
                            format!("[{}]", vals)
                        }
                        Delimiter::None => {
                            let vals = Self::parse_token_stream(group.stream())?.join("");
                            format!("{}", vals)
                        }
                    }
                }
                TokenTree::Ident(ident) => format!("{} ", ident.to_string()),
                TokenTree::Punct(punct) => {
                    format!("{}", punct.to_string())
                },
                TokenTree::Literal(literal) => literal.to_string(),
            })
        }
        fn parse_stmts(t: TokenStream) -> Result<Vec<String>> {
            let mut stmts = vec![];
            let mut iter = t.into_iter();
            #[derive(Debug)]
            enum State {
                LookingForStmt,
                ReadingDirective,
                ReadingPunct(Vec<char>),
                ReadingStmt(String),
            }
            let mut state = State::LookingForStmt;
            while let Some(tt) = iter.next() {
                state = match (state, tt) {
                    (State::LookingForStmt, TokenTree::Punct(p)) if p.as_char() == '#' => {
                        State::ReadingDirective
                    }
                    (State::ReadingDirective, TokenTree::Ident(i)) if i == "if" => {
                        let Some(TokenTree::Ident(id)) = iter.next() else {
                            return Err(Error::new(i.span(), "invalid #if".into()))
                        };
                        stmts.push(format!("#if {}", id));
                        stmts.push("\n".to_string());
                        State::LookingForStmt
                    }
                    (State::ReadingDirective, TokenTree::Ident(i)) if i == "else" || i == "endif" => {
                        stmts.push(format!("#{}", i));
                        stmts.push("\n".to_string());
                        State::LookingForStmt
                    }
                    (State::LookingForStmt, TokenTree::Punct(p)) if p.as_char() != ';' => {
                        State::ReadingPunct(vec![p.as_char()])
                    }
                    (State::ReadingPunct(mut chars), TokenTree::Punct(p)) if p.as_char() != ';' => {
                        chars.push(p.as_char());
                        State::ReadingPunct(chars)
                    }
                    (State::ReadingPunct(chars), tt) => {
                        let str: String = chars.to_vec().into_iter().collect();
                        State::ReadingStmt(str + &tt.to_string())
                    }
                    (State::ReadingStmt(stmt), TokenTree::Punct(p)) if p.as_char() == ';' => {
                        stmts.push(stmt + ";");
                        stmts.push("\n".to_string());
                        State::LookingForStmt
                    }
                    (State::ReadingStmt(stmt), tt) => {
                        State::ReadingStmt(stmt + &tt.to_string())
                    }
                    (State::LookingForStmt, tt) => {
                        stmts.push(tt.to_string());
                        stmts.push(" ".to_string());
                        State::LookingForStmt
                    }
                    x => {
                        println!("// ENDED {:?}", x);
                        break
                    },
                }
            }
            Ok(stmts)
        }
    }
}