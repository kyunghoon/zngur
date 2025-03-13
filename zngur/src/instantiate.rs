use std::collections::HashMap;
use proc_macro2::Span;
use quote::{quote, ToTokens};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_quote, FnArg, Generics, Ident, ImplItem, ImplItemFn, ItemEnum, ItemImpl, ItemStruct, Path, ReturnType, Token, Type};
use crate::types;
use super::parser::remove_semicolon;
use super::Result;

pub struct Instantiate<'a> {
    cratepath: &'a Option<Path>,
    env: &'a HashMap<&'a Ident, &'a Type>,
}
impl<'a> Instantiate<'a> {
    pub fn new(cratepath: &'a Option<Path>, env: &'a HashMap<&'a Ident, &'a Type>) -> Self {
        Self { cratepath, env }
    }
    fn impl_fn_inplace(&self, item: &mut ImplItemFn) -> Result<()> {
        if let ReturnType::Type(_, ty) = &mut item.sig.output {
            *ty = Box::new(self.ty(*ty.clone()));
        }
        for input in item.sig.inputs.iter_mut() {
            if let FnArg::Typed(pat_type) = input {
                pat_type.ty = Box::new(self.ty(*pat_type.ty.clone()));
            }
        }
        Ok(())
    }
    pub fn item_impl(&self, item: &ItemImpl) -> Result<ItemImpl> {
        let mut item = item.clone();
        for i in &mut item.items {
            match i {
                ImplItem::Fn(f) => {
                    self.impl_fn_inplace(f)?;
                },
                ImplItem::Verbatim(token_stream) => {
                    let ts = remove_semicolon(token_stream.clone())?;
                    let mut f: ImplItemFn = parse_quote! { #ts { unimplemented!() } };
                    self.impl_fn_inplace(&mut f)?;
                    let ImplItemFn { attrs, vis, sig, .. } = f;
                    *token_stream = ImplItem::Verbatim(quote! { #(#attrs),* #vis #sig; }).to_token_stream();
                }
                _ => ()
            }
        }
        Ok(item)
    }
    pub fn item_enum(&self, item: &ItemEnum) -> Option<ItemEnum> {
        let mut item = item.clone();
        item.generics.params.clear();
        item.variants.iter_mut().for_each(|v|
            v.fields.iter_mut().for_each(|f|
                f.ty = self.ty(f.ty.clone())));
        Some(item)
    }
    fn ty(&self, ty: Type) -> Type {
        let ty = if let Type::Path(p) = ty {
            if let Some(arg) = p.path.get_ident().and_then(|i| self.env.get(i)) {
                (*arg).clone()
            } else {
                Type::Path(p)
            }
        } else {
            ty
        };
        let mp: Punctuated<_, Token![::]> = self.cratepath.as_ref().map(|p| p.segments.iter().map(|s| &s.ident).collect::<Punctuated<_, _>>()).unwrap_or_default();
        //let mp: Punctuated::<_, Token![::]> = self.cratepath.iter().map(|s| Ident::new(&s, ty.span())).collect();
        types::map_type_paths_and_lifetimes(ty, &mut |tp| {
            if tp.path.leading_colon.is_some() { tp } else {
                parse_quote!(crate::#mp::#tp)
            }
        }, None)
    }
}

pub trait Instantiatable : Sized {
    fn get_span(&self) -> Span;
    fn ident(&self) -> &Ident;
    fn generics(&self) -> &Generics;
    fn instantiate(&self, params: &Vec<Ident>, args: &Vec<Type>, cratepath: &Option<Path>, imp: Option<&ItemImpl>) -> Result<Option<(Self, Option<ItemImpl>)>> {
        let env = params.iter().map(|i| i).zip(args.iter()).collect::<HashMap<_, _>>();
        let inst = Instantiate::new(cratepath, &env);
        if let Some(item) = self.instantiate_type(&inst) {
            let instantiated_impl = imp.map(|i| self.instantiate_impl(&inst, i)).transpose()?;
            Ok(Some((item, instantiated_impl)))
        } else {
            Ok(None)
        }
    }
    fn instantiate_type(&self, inst: &Instantiate) -> Option<Self>;
    fn instantiate_impl(&self, inst: &Instantiate, imp: &ItemImpl) -> Result<ItemImpl>;
}
impl Instantiatable for ItemEnum {
    fn get_span(&self) -> Span { self.span() }
    fn ident(&self) -> &Ident { &self.ident }
    fn generics(&self) -> &Generics { &self.generics }
    fn instantiate_type(&self, inst: &Instantiate) -> Option<Self> {
        let mut item = self.clone();
        // item.generics.params.clear();
        item.variants.iter_mut().for_each(|v|
            v.fields.iter_mut().for_each(|f|
                f.ty = inst.ty(f.ty.clone())));
        Some(item)
    }
    fn instantiate_impl(&self, inst: &Instantiate, imp: &ItemImpl) -> Result<ItemImpl> {
        inst.item_impl(imp)
    }
}

impl Instantiatable for ItemStruct {
    fn get_span(&self) -> Span { self.span() }
    fn ident(&self) -> &Ident { &self.ident }
    fn generics(&self) -> &Generics { &self.generics }
    fn instantiate_type(&self, _inst: &Instantiate) -> Option<Self> {
        let mut item = self.clone();
        // item.generics.params.clear();
        Some(item)
    }

    fn instantiate_impl(&self, inst: &Instantiate, imp: &ItemImpl) -> Result<ItemImpl> {
        inst.item_impl(imp)
    }
}