//! This crate contains an API for using the Zngur code generator inside build scripts. For more information
//! about the Zngur itself, see [the documentation](https://hkalbasi.github.io/zngur).

mod parser;
mod types;
mod instantiate;
mod cppwriter;

use std::{
    borrow::Cow, collections::BTreeMap, fs::File, io::Write, path::{Path, PathBuf}
};

use proc_macro2::{Span, TokenStream};
use syn::{parse_quote, Expr, ExprLit, ExprTuple, Ident, Item, ItemMod, Lit};
use zngur_generator::{ParsedZngFile, ZngurGenerator};
use quote::{quote, ToTokens};

pub use parser::{Parser, ParseMode};
pub use cppwriter::CppWriter;

#[derive(Debug)]
pub struct Error(pub Span, pub Cow<'static, str>);
impl Error { pub fn new(span: Span, msg: Cow<'static, str>) -> Self { Self(span, msg.into()) } }
impl Into<TokenStream> for Error { fn into(self) -> TokenStream { syn::Error::new(self.0, format!("uegen-error: {}", self.1)).to_compile_error().to_token_stream().into() } }
impl From<syn::Error> for Error { fn from(value: syn::Error) -> Self { Self(value.span(), Cow::Owned(value.to_string())) } }
type Result<T> = std::result::Result<T, Error>;

#[must_use]
/// Builder for the Zngur generator.
///
/// Usage:
/// ```ignore
/// let crate_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
/// let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
/// Zngur::from_zng_file(crate_dir.join("main.zng"))
///     .with_cpp_file(out_dir.join("generated.cpp"))
///     .with_h_file(out_dir.join("generated.h"))
///     .with_rs_file(out_dir.join("generated.rs"))
///     .generate();
/// ```
pub struct Zngur {
    zng_file: PathBuf,
    h_file_path: Option<PathBuf>,
    cpp_file_path: Option<PathBuf>,
    rs_file_path: Option<PathBuf>,
}

impl Zngur {
    pub fn from_zng_file(zng_file_path: impl AsRef<Path>) -> Self {
        Zngur {
            zng_file: zng_file_path.as_ref().to_owned(),
            h_file_path: None,
            cpp_file_path: None,
            rs_file_path: None,
        }
    }

    pub fn with_h_file(mut self, path: impl AsRef<Path>) -> Self {
        self.h_file_path = Some(path.as_ref().to_owned());
        self
    }

    pub fn with_cpp_file(mut self, path: impl AsRef<Path>) -> Self {
        self.cpp_file_path = Some(path.as_ref().to_owned());
        self
    }

    pub fn with_rs_file(mut self, path: impl AsRef<Path>) -> Self {
        self.rs_file_path = Some(path.as_ref().to_owned());
        self
    }

    pub fn generate(self) {
        let path = self.zng_file;
        let file = std::fs::read_to_string(path).unwrap();
        let file = ZngurGenerator::build_from_zng(ParsedZngFile::parse("main.zng", &file));

        let (rust, h, cpp) = file.render();
        if let Some(rs_file_path) = self.rs_file_path {
            File::create(rs_file_path)
                .unwrap()
                .write_all(rust.as_bytes())
                .unwrap();
        }
        if let Some(h_file_path) = self.h_file_path {
            File::create(&h_file_path)
                .expect(&format!("failed to create file '{h_file_path:?}"))
                .write_all(h.as_bytes())
                .unwrap();
        }
        if let Some(cpp) = cpp {
            if let Some(cpp_file_path) = self.cpp_file_path {
                File::create(cpp_file_path)
                    .unwrap()
                    .write_all(cpp.as_bytes())
                    .unwrap();
            }
        }
    }

    pub fn create_parser(
        additional_includes: &[&str],
        prelude_types: &[&str],
    ) -> Parser {
        let additional_includes = additional_includes.iter().map(|i| i.to_string()).collect::<Vec<_>>();
        let Some(prelude_types) = prelude_types.iter().map(|pair| {
            let pair: TokenStream = pair.parse().ok()?;
            let expr: ExprTuple = parse_quote!(#pair);
            let mut ei = expr.elems.into_iter();
            let Some(Expr::Lit(ExprLit { lit: Lit::Str(s), .. })) = ei.next() else { return None };
            let key = Ident::new(&s.value(), Span::call_site());
            let vals = ei.map(|i| {
                let Expr::Lit(ExprLit { lit: Lit::Str(s), .. }) = i else { return None };
                Some(Ident::new(&s.value(), Span::call_site()))
            }).collect::<Option<Vec<_>>>()?;
            Some((key, vals))
        }).collect::<Option<BTreeMap<_, _>>>() else {
            panic!("failed to parse prelude_types");
        };

        Parser::new(&additional_includes, prelude_types)
    }

    pub fn parse(
        parser: &mut Parser,
        token_stream_string: &str,
        layouts: &[(usize, usize, usize, usize)],
        on_mod: &mut impl FnMut(String, String),
    ) -> String {
        let tokens: TokenStream = token_stream_string.parse().unwrap();
        let item: ItemMod = parse_quote!( #tokens );

        let items = parser.parse(item).expect("parse failed");

        let mut zngur_output = parser.output();
        for (size_of, align_of, linenum, indent) in layouts.iter() {
            if let Some(line) = zngur_output.get_mut(*linenum) {
                if !line.trim_start().starts_with("#layout") {
                    eprintln!("WARNING corrupt layout detected '{}'", line);
                }
                let indent = (0..*indent).map(|_| "    ").collect::<Vec<_>>().join("");
                *line = format!("{}#layout(size = {}, align = {});\n", indent, size_of, align_of).to_string();
            }
        }

        for item in items {
            if let Item::Mod(item_mod) = item {
                if let Some((_, items)) = item_mod.content {
                    let ts: proc_macro2::TokenStream = quote! { #(#items)* };
                    let file: syn::File = syn::parse2(ts).expect("syn parse failed");
                    let contents = format!("// This file has been generated by zgen\n#![allow(unused_imports)]\n#![allow(dead_code)]\n\n{}", prettyplease::unparse(&file));
                    on_mod(item_mod.ident.to_string(), contents);

                }
            }
        }

        zngur_output.join("")
    }
}
