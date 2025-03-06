use std::collections::HashMap;
use quote::{quote, ToTokens};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_quote, FnArg, Ident, ImplItem, ImplItemFn, ItemEnum, ItemImpl, ReturnType, Token, Type};
use super::parser::{Parser, remove_semicolon};
use super::Result;

pub struct Instantiate<'a> {
    modpath: &'a Vec<String>,
    env: &'a HashMap<&'a Ident, &'a Type>,
}
impl<'a> Instantiate<'a> {
    pub fn new(modpath: &'a Vec<String>, env: &'a HashMap<&'a Ident, &'a Type>) -> Self {
        Self { modpath, env }
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
        let mp: Punctuated::<_, Token![::]> = self.modpath.iter().map(|s| Ident::new(&s, ty.span())).collect();
        Parser::map_type_paths(ty, &mut |p| {
            if p.leading_colon.is_some() { p } else {
                parse_quote!(crate::#mp::#p)
            }
        }, None)
    }
}