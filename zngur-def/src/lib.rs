use std::{collections::BTreeMap, fmt::Display};

use itertools::Itertools;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mutability {
    Mut,
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ZngurMethodReceiver {
    Static,
    Ref(Mutability, Option<String>),
    Move,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZngurMethod {
    pub name: String,
    pub generics: Vec<RustType>,
    pub receiver: ZngurMethodReceiver,
    pub inputs: Vec<RustType>,
    pub output: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZngurFn {
    pub has_receiver: bool,
    pub path: RustPathAndGenerics,
    pub inputs: Vec<RustType>,
    pub output: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZngurExternCppFn {
    pub name: String,
    pub inputs: Vec<RustType>,
    pub output: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZngurExternCppImpl {
    pub tr: Option<RustTrait>,
    pub ty: RustType,
    pub methods: Vec<ZngurMethod>,
    pub lifetimes: Vec<String>,
}

pub struct ZngurConstructor {
    pub name: Option<String>,
    pub inputs: Vec<(String, RustType)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ZngurWellknownTrait {
    Debug,
    Drop,
    Unsized,
    Copy,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ZngurWellknownTraitData {
    Debug {
        pretty_print: String,
        debug_print: String,
    },
    Drop {
        drop_in_place: String,
    },
    Unsized,
    Copy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayoutPolicy {
    StackAllocated { size: usize, align: usize },
    HeapAllocated,
    OnlyByRef,
}

pub struct ZngurMethodDetails {
    pub data: ZngurMethod,
    pub use_path: Option<Vec<String>>,
    pub deref: Option<RustType>,
}

pub struct ZngurType {
    pub ty: RustType,
    pub layout: LayoutPolicy,
    pub wellknown_traits: Vec<ZngurWellknownTrait>,
    pub methods: Vec<ZngurMethodDetails>,
    pub constructors: Vec<ZngurConstructor>,
    pub cpp_value: Option<(String, String)>,
    pub cpp_ref: Option<String>,
    pub rust_value: Option<(String, String)>,
    pub alias: Option<RustType>,
}

pub struct ZngurTrait {
    pub tr: RustTrait,
    pub methods: Vec<ZngurMethod>,
}

#[derive(Default)]
pub struct ZngurFile {
    pub types: Vec<ZngurType>,
    pub traits: BTreeMap<RustTrait, ZngurTrait>,
    pub funcs: Vec<ZngurFn>,
    pub extern_cpp_funcs: Vec<ZngurExternCppFn>,
    pub extern_cpp_impls: Vec<ZngurExternCppImpl>,
    pub additional_includes: String,
    pub convert_panic_to_exception: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RustTrait {
    Normal(RustPathAndGenerics),
    Fn {
        name: String,
        inputs: Vec<RustType>,
        output: Box<RustType>,
    },
}

impl RustTrait {
    pub fn take_assocs(mut self) -> (Self, Vec<(String, RustType)>) {
        let assocs = match &mut self {
            RustTrait::Normal(p) => std::mem::take(&mut p.named_generics),
            RustTrait::Fn { .. } => vec![],
        };
        (self, assocs)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveRustType {
    Uint(u32),
    Int(u32),
    Float(u32),
    Usize,
    Bool,
    Str,
    ZngurCppOpaqueOwnedObject,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RustType {
    Primitive(PrimitiveRustType),
    Ref(Mutability, Box<RustType>, Option<String>),
    Raw(Mutability, Box<RustType>),
    Boxed(Box<RustType>),
    Slice(Box<RustType>),
    Dyn(RustTrait, Vec<String>),
    Tuple(Vec<RustType>),
    Adt(RustPathAndGenerics),
    Enum(RustEnum),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RustEnum {
    pub path: Vec<String>,
    pub wrapped: bool,
}

impl Display for RustEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for p in &self.path {
            if p != "crate" {
                write!(f, "::")?;
            }
            write!(f, "{p}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RustPathAndGenerics {
    pub path: Vec<String>,
    pub generics: Vec<RustType>,
    pub named_generics: Vec<(String, RustType)>,
    pub lifetimes: Vec<String>,
}

impl Display for RustPathAndGenerics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let RustPathAndGenerics {
            path,
            generics,
            named_generics,
            ..
        } = self;
        for p in path {
            if p != "crate" {
                write!(f, "::")?;
            }
            write!(f, "{p}")?;
        }
        if !generics.is_empty() || !named_generics.is_empty() {
            write!(
                f,
                "::<{}>",
                generics.iter().map(|x| format!("{x}"))
                .chain(named_generics.iter().map(|x| format!("{} = {}", x.0, x.1)))
                .join(", ")
            )?;
        }
        Ok(())
    }
}

impl Display for RustTrait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RustTrait::Normal(tr) => write!(f, "{tr}"),
            RustTrait::Fn {
                name,
                inputs,
                output,
            } => {
                write!(f, "{name}({})", inputs.iter().join(", "))?;
                if **output != RustType::UNIT {
                    write!(f, " -> {}", OutputRustTypeWrapper::new(&output))?;
                }
                Ok(())
            }
        }
    }
}

impl Display for RustType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RustType::Primitive(s) => match s {
                PrimitiveRustType::Uint(s) => write!(f, "u{s}"),
                PrimitiveRustType::Int(s) => write!(f, "i{s}"),
                PrimitiveRustType::Float(s) => write!(f, "f{s}"),
                PrimitiveRustType::Usize => write!(f, "usize"),
                PrimitiveRustType::Bool => write!(f, "bool"),
                PrimitiveRustType::Str => write!(f, "str"),
                PrimitiveRustType::ZngurCppOpaqueOwnedObject => {
                    write!(f, "ZngurCppOpaqueOwnedObject")
                }
            },
            RustType::Ref(Mutability::Not, ty, None) => write!(f, "&{ty}"),
            RustType::Ref(Mutability::Not, ty, Some(lt)) => write!(f, "&'{lt} {ty}"),
            RustType::Ref(Mutability::Mut, ty, None) => write!(f, "&mut {ty}"),
            RustType::Ref(Mutability::Mut, ty, Some(lt)) => write!(f, "&'{lt} mut {ty}"),
            RustType::Raw(Mutability::Not, ty) => write!(f, "*const {ty}"),
            RustType::Raw(Mutability::Mut, ty) => write!(f, "*mut {ty}"),
            RustType::Boxed(ty) => write!(f, "Box<{ty}>"),
            RustType::Tuple(v) => write!(f, "({})", v.iter().join(", ")),
            RustType::Adt(pg) => write!(f, "{pg}"),
            RustType::Enum(e) => write!(f, "{e}"),
            RustType::Dyn(tr, marker_bounds) => {
                write!(f, "dyn {tr}")?;
                for mb in marker_bounds {
                    write!(f, "+ {mb}")?;
                }
                Ok(())
            }
            RustType::Slice(s) => write!(f, "[{s}]"),
        }
    }
}

pub struct OutputRustTypeWrapper<'a> { ty: &'a RustType }
impl<'a> OutputRustTypeWrapper<'a> { pub fn new(ty: &'a RustType) -> Self { Self { ty } } }
impl<'a> Display for OutputRustTypeWrapper<'a> {
    #[cfg(not(feature = "mut-guard"))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.ty.fmt(f)
    }
    #[cfg(feature = "mut-guard")]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.ty.to_mut_guard_type().fmt(f)
    }
}

impl RustType {
    pub const UNIT: Self = RustType::Tuple(Vec::new());
    pub fn has_ref_mut(&self) -> bool {
        match self {
            RustType::Ref(Mutability::Mut, rust_type, _) if matches!(**rust_type, RustType::Adt(..)) => true,
            RustType::Adt(RustPathAndGenerics { generics, named_generics, .. }) =>
                generics.iter().chain(named_generics.iter().map(|(_, ty)| ty)).any(|ty| ty.has_ref_mut()),
            _ => false,
        }
    }
    #[cfg(feature = "mut-guard")]
    pub fn to_mut_guard_type(&self) -> RustType {
        match self {
            RustType::Ref(Mutability::Mut, rust_type, v) => {
                match &**rust_type {
                    RustType::Adt(RustPathAndGenerics { path, generics, named_generics, lifetimes }) => {
                        RustType::Adt(RustPathAndGenerics {
                            path: ["crate", "generated", "GuardedMut"].iter().map(|s| s.to_string()).collect(),
                            generics: vec![RustType::Adt(RustPathAndGenerics {
                                path: path.clone(),
                                generics: generics.iter().map(|ty| ty.to_mut_guard_type()).collect(),
                                named_generics: named_generics.iter().map(|(k, ty)| (k.clone(), ty.to_mut_guard_type())).collect(),
                                lifetimes: lifetimes.clone(),
                            })],
                            named_generics: vec![],
                            lifetimes: vec![],
                        })
                    },
                    ty => RustType::Ref(Mutability::Mut, Box::new(ty.clone()), v.clone()),
                }
            }
            RustType::Adt(RustPathAndGenerics { path, generics, named_generics, lifetimes }) => {
                RustType::Adt(RustPathAndGenerics {
                    path: path.clone(),
                    generics: generics.iter().map(|ty| ty.to_mut_guard_type()).collect(),
                    named_generics: named_generics.iter().map(|(k, v)| (k.clone(), v.to_mut_guard_type())).collect(),
                    lifetimes: lifetimes.clone(),
                })
            }
            ty => ty.clone(),
        }
    }
}

pub struct OutputRustConstructorWrapper<'a> { varname: &'a str }
impl<'a> OutputRustConstructorWrapper<'a> { pub fn new(varname: &'a str) -> Self { Self { varname } } }
impl<'a> Display for OutputRustConstructorWrapper<'a> {
    #[cfg(not(feature = "mut-guard"))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{}.assume_init()", self.varname))
    }
    #[cfg(feature = "mut-guard")]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Guard::guard({})", self.varname))
    }
}

