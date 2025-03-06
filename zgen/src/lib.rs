use std::{borrow::Cow, collections::HashMap};
use zngur::{ParseMode, Parser};
use proc_macro2::Span;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, parse_quote, punctuated::Punctuated, Expr, ExprLit, ExprPath, ExprTuple, ItemMod, Lit, Meta, Token};

#[derive(Debug)]
struct Error(Span, Cow<'static, str>);
impl Error { pub fn new(span: Span, msg: Cow<'static, str>) -> Self { Self(span, msg.into()) } }
impl Into<proc_macro::TokenStream> for Error { fn into(self) -> proc_macro::TokenStream { syn::Error::new(self.0, format!("uegen-error: {}", self.1)).to_compile_error().to_token_stream().into() } }
impl From<zngur::Error> for Error { fn from(value: zngur::Error) -> Self { Self(value.0, value.1) } }
impl From<syn::Error> for Error { fn from(value: syn::Error) -> Self { Self(value.span(), Cow::Owned(value.to_string())) } }

fn write_to_file(path: &::std::path::Path, contents: &str) -> ::std::io::Result<()> {
    use ::std::io::Write;
    let mut writer = ::std::io::BufWriter::new(::std::fs::File::create(path)?);
    writeln!(writer, "{contents}")?;
    writer.flush()?;
    Ok(())
}

#[proc_macro_attribute]
pub fn generate(attr: TokenStream, item: TokenStream) -> TokenStream {
    let current_dir = std::env::current_dir().expect("failed to get current_dir");

    let args = parse_macro_input!(attr with Punctuated::<Meta, syn::Token![,]>::parse_terminated);

    let mut full_rs_debug_output_path = None;
    let mut full_rs_output_path = None;
    let mut additional_includes = vec![];
    let mut prelude_types = HashMap::new();
    let mut disabled = false;
    for arg in &args {
        if let Meta::NameValue(name_value) = arg {
            if let Some(ident) = name_value.path.get_ident() {
                match (ident, &name_value.value) {
                    (id, Expr::Lit(ExprLit { lit: Lit::Bool(b), .. })) if id == "disabled" =>
                        disabled = b.value,
                    (id, Expr::Lit(ExprLit { lit: Lit::Str(str), .. })) if id == "rs_debug_output_path" =>
                        full_rs_debug_output_path = Some(current_dir.join(str.value())),
                    (id, Expr::Lit(ExprLit { lit: Lit::Str(str), .. })) if id == "rs_output_path" =>
                        full_rs_output_path = Some(current_dir.join(str.value())),
                    (id, Expr::Tuple(ExprTuple { elems, .. })) if id == "cpp_additional_includes" => {
                        for elem in elems {
                            if let Expr::Lit(ExprLit { lit: Lit::Str(token), .. }) = elem {
                                additional_includes.push(token.value());
                            }
                        }
                    }
                    (id, Expr::Tuple(ExprTuple { elems, .. })) if id == "prelude_types" => {
                        for elem in elems {
                            if let Expr::Path(ExprPath { path, .. }) = elem {
                                let mut segs = path.clone().segments.into_iter().map(|s| s.ident).collect::<Vec<_>>();
                                if let Some(last) = segs.pop() {
                                    if !segs.is_empty() {
                                        prelude_types.insert(last.clone(), segs);
                                    }
                                }
                            }
                        }
                    }
                    _ => ()
                }
            }
        }
    }
    if disabled {
        return quote!{
            pub fn token_stream_string<'a>() -> Option<(&'a str, &'a [(usize, usize, usize, usize)], &'a [&'a str], &'a [&'a str])> {
                None
            }
        }.into();
    }

    let has_generated = full_rs_output_path.as_ref().and_then(|p| std::fs::exists(&p).ok()).unwrap_or_default();

    let item_orig: ItemMod = parse_macro_input!(item);

    let mut parser = Parser::with_details(has_generated, &additional_includes, prelude_types.clone(), false, ParseMode::TypeCheck);
    let mut items = match parser.parse(item_orig.clone()) {
        Err(err) => return Into::<Error>::into(err).into(),
        Ok(items) => items,
    };

    if has_generated {
        items.push(parse_quote! { mod generated; });
    } else {
        items.push(parse_quote! {
            pub mod generated {
                pub struct ZngurCppOpaqueBorrowedObject<T: ?Sized=()>((), std::marker::PhantomData<T>);
                #[repr(C)] pub struct ZngurCppOpaqueOwnedObject<T: ?Sized=()> {
                    data: *mut u8,
                    destructor: extern "C" fn(*mut u8),
                    _marker: std::marker::PhantomData<T>,
                }
            }
        });
    }

    if let Some(path) = &full_rs_debug_output_path {
        let items = items.clone();
        let ts = quote! {
            #![allow(unused_variables)]
            #(#items)* 
        };
        let file: syn::File = match syn::parse2(ts) {
            Err(e) => return Error::new(e.span(), e.to_string().into()).into(),
            Ok(f) => f,
        };
        let contents = prettyplease::unparse(&file);
        if let Err(e) = write_to_file(&path, &contents) {
            return Error::new(Span::call_site(), format!("failed to output rust: {}", e.to_string()).into()).into();
        }
    }

    items.push({
        let toks = item_orig.to_token_stream().to_string();
        let stmts = parser.needed_layouts().into_iter().map(|(ty, linenum, indent)| {
            quote! { (::std::mem::size_of::<#ty>(), ::std::mem::align_of::<#ty>(), #linenum, #indent) }
        });
        let additional = additional_includes.iter();
        let preludes = prelude_types.iter().map(|(k, v)| {
            let key = k.to_token_stream().to_string();
            let vals: Punctuated<String, Token![,]> = v.iter().map(|v| v.to_token_stream().to_string()).collect();
            quote!((#key, #vals)).to_token_stream().to_string()
        });
        parse_quote! {
            pub fn token_stream_string<'a>() -> Option<(&'a str, &'a [(usize, usize, usize, usize)], &'a [&'a str], &'a [&'a str])> {
                fn needed_layouts<'a>() -> &'a [(usize, usize, usize, usize)] {
                    use ue::*;
                    &[#(#stmts),*]
                }
                let add = &[#(#additional),*];
                let pres = &[#(#preludes),*];
                use ue::*;
                Some((#toks, needed_layouts(), add, pres))
            }
        }
    });

    quote! { #(#items)* }.into()
}