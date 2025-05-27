use std::{collections::{HashMap, HashSet}, path::PathBuf};
use syn::{GenericArgument, PathArguments, Type, TypePath, TypeReference};
use zngur_generator::cpp::sanitize_cpp_keywords;

use crate::parser::CppJinjaConfig;

#[derive(Debug)]
pub enum Error {
    BadInputPath(std::path::PathBuf),
    BadTeraOneOff(tera::Error),
}
type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Eq)]
pub enum CppMethodVisibility { Public, Protected, Private }

pub enum CppMethodModifier { Static, None { mutable: bool }, Virtual { mutable : bool } }

pub struct CppMethod {
    pub name: String,
    pub inputs: Vec<(String, Type)>,
    pub output: Option<Type>,
    pub vis: CppMethodVisibility,
    pub modifier: CppMethodModifier,
    pub lines: Vec<String>,
}

pub struct CppJinjaWriter<'a> {
    templates_path: PathBuf,
    class_name: String,
    context: tera::Context,
    methods: Vec<CppMethod>,
    config: CppJinjaConfig,
    type_mappings: &'a HashMap<String, String>,
    enum_types: &'a HashSet<String>,
}
impl<'a> CppJinjaWriter<'a> {
    pub fn new(templates_path: &std::path::Path, class_name: String, initial_context: &HashMap<String, String>, config: CppJinjaConfig, type_mappings: &'a HashMap<String, String>, enum_types: &'a HashSet<String>) -> Self {
        let mut context = tera::Context::new();
        for (k, v) in initial_context.iter() {
            context.insert(k, v);
        }
        Self {
            templates_path: templates_path.to_owned(),
            class_name: type_mappings.get(&class_name).cloned().unwrap_or(class_name),
            context,
            methods: vec![],
            config,
            type_mappings,
            enum_types,
        }
    }
    pub fn add_method(&mut self, method: CppMethod) { self.methods.push(method); }
    pub fn h_path(&self) -> &std::path::Path { &self.config.h_path }
    pub fn cpp_path(&self) -> &std::path::Path { &self.config.cpp_path }
    pub fn h_output(&self) -> Result<String> {
        let Some(jinja_path) = self.config.h_path.to_str() else { return Err(Error::BadInputPath(self.config.h_path.clone())) };
        let jinja_path = format!("{jinja_path}.jinja");
        let contents = std::fs::read_to_string(self.templates_path.join(&jinja_path)).map_err(|_| Error::BadInputPath(jinja_path.into()))?;
        let render_method = |method: &CppMethod| -> String {
            let method_name = sanitize_cpp_keywords(&method.name);
            let params = method.inputs.iter().map(|(n, t)| format!("{} {n}", self.to_cpp_type(t))).collect::<Vec<_>>().join(", ");
            let (modifier, has_const) = match method.modifier {
                CppMethodModifier::Static => ("static ", false),
                CppMethodModifier::None { mutable } => ("", !mutable),
                CppMethodModifier::Virtual { mutable } => ("virtual ", !mutable),
            };
            format!("    {}{} {}({}){};", modifier, method.output.as_ref().map(|t| self.to_cpp_type(t)).unwrap_or("void".into()), method_name, params, if has_const { " const" } else { "" })
        };
        let public_methods = self.methods.iter().filter(|m| m.vis == CppMethodVisibility::Public).map(render_method).collect::<Vec<_>>();
        let protected_methods = self.methods.iter().filter(|m| m.vis == CppMethodVisibility::Protected).map(render_method).collect::<Vec<_>>();
        let private_methods = self.methods.iter().filter(|m| m.vis == CppMethodVisibility::Private).map(render_method).collect::<Vec<_>>();
        let stmts = format!("public:\n{}\nprotected:\n{}\nprivate:\n{}\n",
            public_methods.join("\n"),
            protected_methods.join("\n"),
            private_methods.join("\n")
        );
        let mut context = self.context.clone();
        context.insert("stmts", &stmts);
        tera::Tera::one_off(&contents, &context, false).map_err(|e| Error::BadTeraOneOff(e))
    }
    pub fn cpp_output(&self) -> Result<String> {
        let Some(jinja_path) = self.config.cpp_path.to_str() else { return Err(Error::BadInputPath(self.config.cpp_path.clone())) };
        let jinja_path = format!("{jinja_path}.jinja");
        let contents = std::fs::read_to_string(self.templates_path.join(&jinja_path)).map_err(|_| Error::BadInputPath(jinja_path.into()))?;
        let mut context = self.context.clone();
        let methods = self.methods.iter().map(|method| {
            let has_const = match method.modifier {
                CppMethodModifier::Static => false,
                CppMethodModifier::None { mutable } => !mutable,
                CppMethodModifier::Virtual { mutable } => !mutable,
            };
            let method_name = sanitize_cpp_keywords(&method.name);
            let params = method.inputs.iter().map(|(n, t)| format!("{} {n}", self.to_cpp_type(t))).collect::<Vec<_>>().join(", ");
            let mut body = method.lines.join("\n    ");
            if !body.is_empty() { body = "\n    ".to_string() + &body + "\n"; }
            format!("{} {}::{}({}){} {{{}}}", method.output.as_ref().map(|t| self.to_cpp_type(t)).unwrap_or("void".into()), self.class_name, method_name, params, if has_const { " const" } else { "" }, body)
        }).collect::<Vec<_>>();
        context.insert("stmts", &methods.join("\n"));
        tera::Tera::one_off(&contents, &context, false).map_err(|e| Error::BadTeraOneOff(e))
    }
    fn to_cpp_type(&self, ty: &Type) -> String {
        match ty {
            Type::Path(TypePath { qself: None, path }) if path.is_ident("i8") => "::int8_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("i16") => "::int16_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("i32") => "::int32".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("i64") => "::int64_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("u8") => "::uint8_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("u16") => "::uint16_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("u32") => "::uint32_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("u64") => "::uint64_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("usize") => "::size_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("isize") => "std::ptr_diff_t".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("f32") => "float".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("f64") => "double".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.is_ident("bool") => "bool".to_string(),
            Type::Path(TypePath { qself: None, path }) if path.get_ident().is_some() => {
                let typename = path.get_ident().unwrap().to_string();
                if self.enum_types.contains(&typename) {
                    format!("{typename}::Type")
                } else {
                    self.type_mappings.get(&typename).cloned().unwrap_or(typename)
                }
            }
            Type::Path(TypePath { qself: None, path }) => {
                let mut si = path.segments.iter();
                match (si.next(), si.next()) {
                    (Some(s1), None) if s1.ident == "Option" => {
                        match &s1.arguments {
                            PathArguments::AngleBracketed(args) => {
                                let mut ai = args.args.iter();
                                match (ai.next(), ai.next()) {
                                    (Some(GenericArgument::Type(ty)), None) => {
                                        match ty {
                                            Type::Reference(TypeReference { mutability, elem, .. }) => {
                                                if mutability.is_some() {
                                                    format!("{}*", self.to_cpp_type(&*elem))
                                                } else {
                                                    format!("{} const*", self.to_cpp_type(&*elem))
                                                }
                                            }
                                            Type::Path(TypePath { qself: None, path }) => {
                                                let mut si = path.segments.iter();
                                                match (si.next(), si.next()) {
                                                    (Some(s1), None) if s1.ident == "SharedRef" => {
                                                        match &s1.arguments {
                                                            PathArguments::AngleBracketed(args) => {
                                                                let mut ai = args.args.iter();
                                                                match (ai.next(), ai.next()) {
                                                                    (Some(GenericArgument::Type(ty)), None) =>
                                                                        format!("TSharedPtr<{} const>", self.to_cpp_type(ty)),
                                                                    _ => format!("/*bad shared ref: {:?}*/", args.args),
                                                                }
                                                            },
                                                            x => format!("/*bad shared ref: {:?}*/", x),
                                                        }
                                                    }
                                                    (Some(s1), None) if s1.ident == "SharedMut" => {
                                                        match &s1.arguments {
                                                            PathArguments::AngleBracketed(args) => {
                                                                let mut ai = args.args.iter();
                                                                match (ai.next(), ai.next()) {
                                                                    (Some(GenericArgument::Type(ty)), None) =>
                                                                        format!("TSharedPtr<{}>", self.to_cpp_type(ty)),
                                                                    _ => format!("/*bad shared mut: {:?}*/", args.args),
                                                                }
                                                            },
                                                            x => format!("/*bad shared mut: {:?}*/", x),
                                                        }
                                                    }
                                                    _ => self.to_cpp_type(ty),
                                                }
                                            }
                                            ty => self.to_cpp_type(ty),
                                        }
                                    },
                                    _ => format!("/*[2]{:?}*/", args.args),
                                }
                            },
                            x => format!("/*[3]{:?}*/", x),
                        }
                    },
                    (Some(s1), None) if s1.ident == "SharedRef" => {
                        match &s1.arguments {
                            PathArguments::AngleBracketed(args) => {
                                let mut ai = args.args.iter();
                                match (ai.next(), ai.next()) {
                                    (Some(GenericArgument::Type(ty)), None) =>
                                        format!("TSharedRef<{} const>", self.to_cpp_type(ty)),
                                    _ => format!("/*bad shared ref: {:?}*/", args.args),
                                }
                            },
                            x => format!("/*bad shared ref: {:?}*/", x),
                        }
                    }
                    (Some(s1), None) if s1.ident == "SharedMut" => {
                        match &s1.arguments {
                            PathArguments::AngleBracketed(args) => {
                                let mut ai = args.args.iter();
                                match (ai.next(), ai.next()) {
                                    (Some(GenericArgument::Type(ty)), None) =>
                                        format!("TSharedRef<{}>", self.to_cpp_type(ty)),
                                    _ => format!("/*bad shared mut: {:?}*/", args.args),
                                }
                            },
                            x => format!("/*bad shared mut: {:?}*/", x),
                        }
                    }
                    _ => format!("/*[4]{:?}*/", path.segments),
                }
            }
            Type::Reference(TypeReference { mutability, elem, .. }) => {
                if mutability.is_some() {
                    format!("{}&", self.to_cpp_type(&*elem))
                } else {
                    format!("{} const&", self.to_cpp_type(&*elem))
                }
            }
            x => format!("/*[5]{:?}*/", x),
        }
    }
}