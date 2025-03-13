mod env {
    use std::{borrow::Cow, collections::{BTreeMap, HashMap, HashSet}};
    use syn::{parse_quote, punctuated::Punctuated, spanned::Spanned, Ident, Path, PathSegment, Token, TypePath };

    fn remove_prefix_matching_right(left: &Punctuated<PathSegment, Token![::]>, right: &Punctuated<PathSegment, Token![::]>) -> Punctuated<PathSegment, Token![::]> {
        let first_different = left.iter()
            .zip(right.iter())
            .position(|(a, b)| a != b) // Find the first different segment
            .unwrap_or(right.len()); // If all match, trim to `right.len()`
        left.iter().skip(first_different).cloned().collect()
    }

    fn is_crate_path(p: &Path) -> bool {
        p.segments.first().map(|s| s.ident == "crate").unwrap_or_default()
    }

    #[derive(Debug)]
    pub struct TypeEnv {
        pub lookup: HashMap<Path, HashSet<Ident>>,
        pub preludes: BTreeMap<Ident, Path>,
    }

    impl TypeEnv {
        fn prelude_path(&self, ident: &Ident) -> Option<&Path> {
            self.preludes.get(ident)
        }
        fn split_typepath(type_path: &TypePath) -> Option<(Path, TypePath)> {
            let mut type_path = type_path.clone();
            if type_path.path.segments.len() > 1 {
                if let Some(last) = type_path.path.segments.pop() {
                    let p = type_path.path.segments.into_iter().collect::<Punctuated<_, Token![::]>>();
                    type_path.path.segments = vec![last.into_value()].into_iter().collect();
                    if !p.is_empty() {
                        return Some((parse_quote!{ #p }, type_path))
                    }
                }
            }
            None
        }
        fn lookup_contains(&self, p: &Path, type_path: &TypePath) -> Option<bool> {
            assert!(type_path.path.segments.len() == 1);
            if let Some(seg) = type_path.path.segments.last() {
                if let Some(idents) = self.lookup.get(p) {
                    return Some(idents.contains(&seg.ident));
                }
            }
            None
        }
        fn resolve_prelude(&self, type_path: &TypePath) -> Option<&Path> {
            assert!(type_path.path.segments.len() == 1);
            if let Some(seg) = type_path.path.segments.last() {
                return self.prelude_path(&seg.ident);
            }
            None
        }
        fn resolve_typepath(&self, p: &Path, type_path: &TypePath) -> Option<Path> {
            if let Some((p, type_path)) = Self::split_typepath(type_path) {
                self.resolve_typepath(&p, &type_path)
            } else {
                if let Some(contains) = self.lookup_contains(p, type_path) {
                    if contains {
                        return Some(p.clone());
                    } else if let Some(last) = type_path.path.segments.last() {
                        return self.prelude_path(&last.ident).cloned();
                    }
                }
                None
            }
        }
        pub fn to_fully_qualified(&self, type_path: &TypePath, to_full: Option<&Path>, dbg: bool) -> TypePath {
            let p = &type_path.path;
            if let Some(to) = p.leading_colon.is_none().then_some(to_full).flatten() {
                if let Some(resolved_to) = self.resolve_typepath(to, &type_path) {
                    let mut p = p.clone();
                    p.segments = remove_prefix_matching_right(&p.segments, &resolved_to.segments);
                    parse_quote!(#resolved_to::#p)
                } else {
                    parse_quote!(#to::#p)
                }
            } else {
                parse_quote!(#p)
            }
        }
        pub fn from_fully_qualfied(&self, type_path: &TypePath, from_full: Option<&Path>, dbg: bool) -> TypePath {
            let mut type_path = type_path.clone();
            let from_full = if let (Some((path, tp_trunc)), Some(from)) = (TypeEnv::split_typepath(&type_path), from_full.as_ref()) {
                let pc = self.resolve_prelude(&tp_trunc);
                if pc.is_some() {
                    let lc = self.lookup_contains(&path, &tp_trunc);
                    if lc.is_some() {
                        type_path.path.leading_colon = Some(Token![::](type_path.span()));
                        return type_path;
                    } else {
                        Some(Cow::Owned(path))
                    }
                } else {
                    if !is_crate_path(&path) && is_crate_path(from) {
                        type_path.path.leading_colon = Some(Token![::](type_path.span()));
                        None
                    } else {
                        self.resolve_typepath(&path, &tp_trunc).map(Cow::Owned).or(from_full.map(Cow::Borrowed))
                    }
                }
            } else {
                from_full.map(Cow::Borrowed)
            };
            if let Some(from) = from_full.as_ref() {
                type_path.path.segments = remove_prefix_matching_right(&type_path.path.segments, &from.segments);
            }
            type_path
        }
    }
}

use std::collections::{hash_map::Entry, BTreeMap, HashMap, HashSet};
use quote::ToTokens;
use syn::{parse_quote, punctuated::Punctuated, token::PathSep, GenericArgument, Ident, ItemEnum, ItemMod, ItemStruct, ItemUse, Path, PathArguments, PathSegment, ReturnType, Token, Type, TypeArray, TypeBareFn, TypeGroup, TypeParen, TypePath, TypePtr, TypeReference, TypeSlice, TypeTuple };
pub use env::TypeEnv;

pub struct TypeEnvBuilder {
    modstack: Vec<Ident>,
    lookup: HashMap<Path, HashSet<Ident>>,
    preludes: BTreeMap<Ident, Path>,
}
impl TypeEnvBuilder {
    pub fn new(preludes: &BTreeMap<Ident, Vec<Ident>>) -> Self {
        Self {
            modstack: Default::default(),
            lookup: Default::default(),
            preludes: preludes.iter().map(|(ident, p)| {
                let p: Punctuated<_, Token![::]> = p.iter().collect();
                (ident.clone(), parse_quote!(#p))
            }).collect::<BTreeMap<_, _>>(),
        }
    }
    pub fn do_push_mod(&mut self, item_mod: &ItemMod, is_crate_mod: bool) {
        if is_crate_mod {
            self.modstack.push(Ident::new("crate", item_mod.ident.span()));
        }
        self.modstack.push(item_mod.ident.clone());
    }
    pub fn do_pop_mod(&mut self, _item_mod: &ItemMod, is_crate_mod: bool) {
        assert!(!self.modstack.is_empty(), "type env modstack undeflow");
        self.modstack.pop();
        if is_crate_mod {
            assert!(!self.modstack.is_empty(), "type env modstack undeflow (crate)");
            self.modstack.pop();
        }
    }
    pub fn do_struct(&mut self, item_struct: &ItemStruct) {
        if !self.modstack.is_empty() {
            self.insert(item_struct.ident.clone(), None);
        }
    }
    pub fn do_use(&mut self, item_use: &ItemUse) {
        if !self.modstack.is_empty() {
            println!("cargo:warning=USE {} ({})", item_use.tree.to_token_stream(), self.path().to_token_stream());
        }
    }
    pub fn do_enum(&mut self, item_enum: &ItemEnum) {
        if !self.modstack.is_empty() {
            self.insert(item_enum.ident.clone(), None);
        }
    }
    fn path(&self) -> Path {
        let p = self.modstack.iter().collect::<Punctuated<_, Token![::]>>();
        parse_quote!{ #p }
    }
    fn insert(&mut self, ident: Ident, path: Option<Path>) {
        if !self.modstack.is_empty() {
            match self.lookup.entry(path.unwrap_or_else(|| self.path())) {
                Entry::Occupied(mut occupied_entry) => {
                    occupied_entry.get_mut().insert(ident);
                }
                Entry::Vacant(vacant_entry) => {
                    let mut idents = HashSet::new();
                    idents.insert(ident);
                    vacant_entry.insert(idents);
                }
            }
        }
    }
    pub fn build(self) -> TypeEnv {
        TypeEnv { lookup: self.lookup, preludes: self.preludes }
    }
}

pub fn map_type_paths(ty: Type, on_typepath: &mut impl FnMut(TypePath) -> TypePath) -> Type {
    match ty {
        Type::Array(TypeArray { bracket_token, elem, semi_token, len }) => 
            Type::Array(TypeArray { bracket_token, elem: Box::new(map_type_paths(*elem, on_typepath)), semi_token, len }),
        Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token, inputs, variadic, output }) =>
            Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token,
                inputs: inputs.into_iter().map(|mut i| { i.ty = map_type_paths(i.ty, on_typepath); i }).collect(),
                variadic, 
                output: match output {
                    ReturnType::Type(rarrow, ty) => ReturnType::Type(rarrow, Box::new(map_type_paths(*ty, on_typepath))),
                    x => x
            }
        }),
        Type::Group(TypeGroup { group_token, elem }) => 
            Type::Group(TypeGroup { group_token, elem: Box::new(map_type_paths(*elem, on_typepath)) }),
        Type::Paren(TypeParen { paren_token, elem }) =>
            Type::Paren(TypeParen { paren_token, elem: Box::new(map_type_paths(*elem, on_typepath)) }),
        Type::Path(mut type_path) => {
            type_path.path.segments = type_path.path.segments.into_iter().map(|mut s| {
                s.arguments = match s.arguments {
                    PathArguments::AngleBracketed(mut gargs) => {
                        gargs.args = gargs.args.into_iter().map(|a| {
                            match a {
                                GenericArgument::Type(ty) =>
                                    GenericArgument::Type(map_type_paths(ty, on_typepath)),
                                x => x,
                            }
                        }).collect();
                        PathArguments::AngleBracketed(gargs)
                    }
                    x => x,
                };
                s
            }).collect();
            Type::Path(on_typepath(type_path))
        },
        Type::Ptr(TypePtr { star_token, const_token, mutability, elem }) =>
            Type::Ptr(TypePtr { star_token, const_token, mutability, elem: Box::new(map_type_paths(*elem, on_typepath)) }),
        Type::Reference(TypeReference { and_token, lifetime, mutability, elem }) =>
            Type::Reference(TypeReference { and_token, lifetime, mutability, elem: Box::new(map_type_paths(*elem, on_typepath)) }),
        Type::Slice(TypeSlice { bracket_token, elem }) =>
            Type::Slice(TypeSlice { bracket_token, elem: Box::new(map_type_paths(*elem, on_typepath)) }),
        Type::Tuple(TypeTuple { paren_token, elems }) =>
            Type::Tuple(TypeTuple { paren_token, elems: elems.into_iter().map(|e| map_type_paths(e, on_typepath)).collect() }),
        x => x
    }
}


pub fn map_type_paths_and_lifetimes(ty: Type, on_typepath: &mut impl FnMut(TypePath) -> TypePath, lts: Option<&HashSet<Ident>>) -> Type {
    match ty {
        Type::Array(TypeArray { bracket_token, elem, semi_token, len }) => 
            Type::Array(TypeArray { bracket_token, elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts)), semi_token, len }),
        Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token, inputs, variadic, output }) =>
            Type::BareFn(TypeBareFn { lifetimes, unsafety, abi, fn_token, paren_token,
                inputs: inputs.into_iter().map(|mut i| { i.ty = map_type_paths_and_lifetimes(i.ty, on_typepath, lts); i }).collect(),
                variadic, 
                output: match output {
                    ReturnType::Type(rarrow, ty) => ReturnType::Type(rarrow, Box::new(map_type_paths_and_lifetimes(*ty, on_typepath, lts))),
                    x => x
            }
        }),
        Type::Group(TypeGroup { group_token, elem }) => 
            Type::Group(TypeGroup { group_token, elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts)) }),
        Type::Paren(TypeParen { paren_token, elem }) =>
            Type::Paren(TypeParen { paren_token, elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts)) }),
        Type::Path(mut type_path) => {
            if let Some(last) = type_path.path.segments.pop() {
                let mut value = last.into_value();
                value.arguments = match value.arguments {
                    PathArguments::AngleBracketed(mut gargs) => {
                        gargs.args = gargs.args.into_iter().filter_map(|a| {
                            match a {
                                GenericArgument::Lifetime(lt) if lt.ident == "static" || lts.map(|l| l.contains(&lt.ident)).unwrap_or_default() => {
                                    Some(GenericArgument::Lifetime(lt))
                                }
                                GenericArgument::Type(ty) =>
                                    Some(GenericArgument::Type(map_type_paths_and_lifetimes(ty, on_typepath, lts))),
                                _ => None,
                            }
                        }).collect();
                        if gargs.args.is_empty() { PathArguments::None } else { PathArguments::AngleBracketed(gargs) }
                    }
                    x => x,
                };
                type_path.path.segments.push(value);
            }
            Type::Path(on_typepath(type_path))
        },
        Type::Ptr(TypePtr { star_token, const_token, mutability, elem }) =>
            Type::Ptr(TypePtr { star_token, const_token, mutability, elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts)) }),
        Type::Reference(TypeReference { and_token, lifetime, mutability, elem }) =>
            Type::Reference(TypeReference {
                and_token,
                lifetime: match (lts, lifetime) {
                    (_, Some(lt)) if lt.ident == "static" =>  Some(lt),
                    (Some(list), Some(lt)) => 
                        if list.contains(&lt.ident) { Some(lt) } else { None },
                    _ => None,
                },
                mutability,
                elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts))
            }),
        Type::Slice(TypeSlice { bracket_token, elem }) =>
            Type::Slice(TypeSlice { bracket_token, elem: Box::new(map_type_paths_and_lifetimes(*elem, on_typepath, lts)) }),
        Type::Tuple(TypeTuple { paren_token, elems }) =>
            Type::Tuple(TypeTuple { paren_token, elems: elems.into_iter().map(|e| map_type_paths_and_lifetimes(e, on_typepath, lts)).collect() }),
        x => x
    }
}

pub fn to_type(ident: &Ident, type_args: Option<&HashMap<Ident, Type>>) -> Type {
    if let Some(args) = type_args {
        let args: Punctuated<_, Token![,]> = args.values().collect();
        parse_quote!{ #ident<#args> }
    } else {
        parse_quote!{ #ident }
    }
}

pub fn to_fully_qualified(ty: Type, to_full: Option<&Path>, ty_env: Option<&TypeEnv>, dbg: bool, lts: Option<&HashSet<Ident>>) -> Type {
    map_type_paths_and_lifetimes(ty, &mut |type_path| {
        ty_env.map(|env| env.to_fully_qualified(&type_path, to_full, dbg)).unwrap_or(type_path)
    }, lts)
}

pub fn from_fully_qualified(ty: Type, from_full: Option<&Path>, ty_env: Option<&TypeEnv>, dbg: bool, lts: Option<&HashSet<Ident>>) -> Type {
    map_type_paths_and_lifetimes(ty, &mut |tp| {
        ty_env.map(|env| env.from_fully_qualfied(&tp, from_full, dbg)).unwrap_or(tp)
    }, lts)
}