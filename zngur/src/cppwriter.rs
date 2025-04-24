use std::{borrow::Cow, collections::{BTreeMap, HashSet}, rc::Rc};
use quote::ToTokens;
use syn::{FnArg, GenericArgument, Ident, Path, PathArguments, PathSegment, ReturnType, Signature, Type, TypeParamBound, TypePtr};

pub struct CppWriter {
    lines: Vec<String>,
    dupcheck: HashSet<(Option<Type>, Ident)>,
    /// Only output `using namespace ..` if the namespace actually has been generated in zngur.
    generated_namespaces: HashSet<Vec<Ident>>,
    pub prelude_types: Rc<BTreeMap<Ident, Vec<Ident>>>,
}
impl CppWriter {
    pub fn new() -> Self { Self {
        lines: vec![],
        dupcheck: Default::default(),
        generated_namespaces: Default::default(),
        prelude_types: Rc::new(Default::default()),
    } }
    pub fn declare_generated_namespace(&mut self, namespace: Vec<Ident>) {
        self.generated_namespaces.insert(namespace);
    }
    #[allow(dead_code)]
    fn add_line(&mut self, modpath: Vec<String>, self_ty: Option<&Type>, trait_: Option<&Path>, sig: &Signature, line: impl ToString) {
        let key = (self_ty.cloned(), sig.ident.clone());
        if self.dupcheck.contains(&key) { return };
        self.dupcheck.insert(key);

        let cpp_sig = self.cpp_sig(&modpath.join("::"), self_ty, trait_, sig);
        self.lines.push(format!("{}", cpp_sig));

        self.lines.push(line.to_string());
        self.lines.push("}".to_string());
    }
    pub fn add_lines(&mut self, modpath: Vec<String>, self_ty: Option<&Type>, trait_: Option<&Path>, sig: &Signature, lines: &[impl ToString]) {
        let key = (self_ty.cloned(), sig.ident.clone());
        if self.dupcheck.contains(&key) { return };
        self.dupcheck.insert(key);

        let cpp_sig = self.cpp_sig(&modpath.join("::"), self_ty, trait_, sig);
        self.lines.push(format!("{}", cpp_sig));

        self.lines.append(&mut lines.into_iter().map(|c| c.to_string()).collect());
        self.lines.push("}".to_string());
    }
    pub fn output(mut self) -> String {
        let mut lines = vec![];
        lines.append(&mut [
            "namespace rust {",
            "    using namespace crate;"
        ].into_iter().map(|s| s.to_string()).collect());
        let preludes = self.prelude_types.iter().filter_map(|(_, modpath)| {
            if !self.generated_namespaces.contains(modpath) { return None };
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
        for p in preludes {
            lines.push(format!("    using namespace {};", p));
        }
        lines.append(&mut self.lines);
        lines.append(&mut [
            "}",
            //"// NOTE: when return RefMut/Ref, matching std::ref/std::cref must be used",
        ].into_iter().map(|s| s.to_string()).collect());
        lines.join("\n")
    }
    fn cpp_sig(&self, modpath: &String, self_ty: Option<&Type>, trait_: Option<&Path>, sig: &Signature) -> String {
        struct Cpp<'a> { prelude_types: &'a BTreeMap<Ident, Vec<Ident>>, modpath: &'a String, self_ty: Option<&'a Type> }
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
                    i if i == "usize" => "::size_t".to_string(),
                    i if i == "isize" => "std::::ptrdeff_t".to_string(),
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
                        a.args.iter().filter_map(|a| match a {
                            GenericArgument::Lifetime(_lifetime) => None,
                            GenericArgument::Type(ty) => Some(format!("{}", self.ty(ty))),
                            GenericArgument::Const(_expr) => Some("TYARGS[3]".to_string()),
                            GenericArgument::AssocType(_assoc_type) => Some("TYARGS[4]".to_string()),
                            GenericArgument::AssocConst(_assoc_const) => Some("TYARGS[5]".to_string()),
                            GenericArgument::Constraint(_constraint) => Some("TYARGS[6]".to_string()),
                            _ => Some("TYARGS[??]".to_string()),
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
                            (Some(a), None) if self.prelude_types.contains_key(&a.ident) => self.path_segment(a),
                            (Some(a), None) => format!("{}::{}", self.modpath, self.path_segment(a)),
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
                    Type::Path(t) if t.path.is_ident("Self") && self.self_ty.is_some() => self.ty(self.self_ty.unwrap()),
                    Type::Path(t) => self.path(&t.path),
                    Type::Ptr(TypePtr { mutability, elem, .. }) => {
                        format!("{}{}*",
                            self.ty(&*elem),
                            if mutability.is_some() { "" } else { " const" },
                        )
                    },
                    Type::Reference(t) => format!("{}<{}>", if t.mutability.is_some() { "RefMut" } else { "Ref" }, self.ty(&*t.elem)),
                    Type::Slice(t) => format!("Slice<{}>", self.ty(&*t.elem)),
                    Type::TraitObject(t) => {
                        let bounds = t.bounds.iter().map(|b| match b {
                            TypeParamBound::Trait(trait_bound) => self.path(&trait_bound.path),
                            TypeParamBound::Lifetime(_l) => "BOUND2".to_string(),
                            TypeParamBound::PreciseCapture(_pc) => "BOUND3".to_string(),
                            TypeParamBound::Verbatim(_ts) => "BOUND4".to_string(),
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

        let cpp = Cpp { prelude_types: &self.prelude_types, modpath, self_ty };

        let output = match &sig.output {
            ReturnType::Default => "void".to_string(),
            ReturnType::Type(_, ty) => cpp.ty(&*ty),
        };

        let inputs = sig.inputs.iter().map(|i| {
            match i {
                FnArg::Receiver(r) => {
                    let ty = cpp.ty(&r.ty);
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

        if let Some(ty) = self_ty {
            let ty = cpp.ty(ty);
            let tr = trait_.map(|p| Cow::Owned(cpp.path(p))).unwrap_or(Cow::Borrowed("Inherent"));
            format!("{} Impl<{}, {}>::{}({}) {{", output, ty, tr, sig_ident, inputs)
        } else {
            format!("{} exported_functions::{}({}) {{", output, sig_ident, inputs)
        }
    }
}

#[allow(dead_code)]
pub mod cpp {
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