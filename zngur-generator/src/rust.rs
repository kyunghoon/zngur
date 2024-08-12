use std::fmt::Write;

use itertools::Itertools;

use crate::{
    cpp::{CppLayoutPolicy, CppPath, CppTraitDefinition, CppTraitMethod, CppType},
    ZngurTrait, ZngurWellknownTrait, ZngurWellknownTraitData,
};

use zngur_def::*;

pub trait IntoCpp {
    fn into_cpp(&self) -> CppType;
}

impl IntoCpp for RustPathAndGenerics {
    fn into_cpp(&self) -> CppType {
        let RustPathAndGenerics {
            path,
            generics,
            named_generics,
            ..
        } = self;
        let named_generics = named_generics.iter().sorted_by_key(|x| &x.0).map(|x| &x.1);
        CppType {
            path: CppPath::from_rust_path(path),
            generic_args: generics
                .iter()
                .chain(named_generics)
                .map(|x| x.into_cpp())
                .collect(),
        }
    }
}

impl IntoCpp for RustTrait {
    fn into_cpp(&self) -> CppType {
        match self {
            RustTrait::Normal(pg) => pg.into_cpp(),
            RustTrait::Fn {
                name,
                inputs,
                output,
            } => CppType {
                path: CppPath::from(&*format!("rust::{name}")),
                generic_args: inputs
                    .iter()
                    .chain(Some(&**output))
                    .map(|x| x.into_cpp())
                    .collect(),
            },
        }
    }
}

impl IntoCpp for RustType {
    fn into_cpp(&self) -> CppType {
        fn for_builtin(this: &RustType) -> Option<CppType> {
            match this {
                RustType::Primitive(s) => match s {
                    PrimitiveRustType::Uint(s) => Some(CppType::from(&*format!("uint{s}_t"))),
                    PrimitiveRustType::Int(s) => Some(CppType::from(&*format!("int{s}_t"))),
                    PrimitiveRustType::Float(32) => Some(CppType::from("float_t")),
                    PrimitiveRustType::Float(64) => Some(CppType::from("double_t")),
                    PrimitiveRustType::Float(_) => unreachable!(),
                    PrimitiveRustType::Usize => Some(CppType::from("size_t")),
                    PrimitiveRustType::Bool | PrimitiveRustType::Str => None,
                    PrimitiveRustType::ZngurCppOpaqueOwnedObject => {
                        Some(CppType::from("rust::ZngurCppOpaqueOwnedObject"))
                    }
                },
                RustType::Raw(Mutability::Mut, t) => Some(CppType::from(&*format!(
                    "{}*",
                    for_builtin(t)?.to_string().strip_prefix("::")?
                ))),
                RustType::Raw(Mutability::Not, t) => Some(CppType::from(&*format!(
                    "{} const*",
                    for_builtin(t)?.to_string().strip_prefix("::")?
                ))),
                _ => None,
            }
        }
        if let Some(builtin) = for_builtin(self) {
            return builtin;
        }
        match self {
            RustType::Primitive(s) => match s {
                PrimitiveRustType::Bool => CppType::from("rust::Bool"),
                PrimitiveRustType::Str => CppType::from("rust::Str"),
                _ => unreachable!(),
            },
            RustType::Boxed(t) => CppType {
                path: CppPath::from("rust::Box"),
                generic_args: vec![t.into_cpp()],
            },
            RustType::Ref(m, t, _) => CppType {
                path: match m {
                    Mutability::Mut => CppPath::from("rust::RefMut"),
                    Mutability::Not => CppPath::from("rust::Ref"),
                },
                generic_args: vec![t.into_cpp()],
            },
            RustType::Slice(s) => CppType {
                path: CppPath::from("rust::Slice"),
                generic_args: vec![s.into_cpp()],
            },
            RustType::Raw(_, _) => todo!(),
            RustType::Adt(pg) => pg.into_cpp(),
            RustType::Tuple(v) => {
                if v.is_empty() {
                    return CppType::from("rust::Unit");
                }
                CppType {
                    path: CppPath::from("rust::Tuple"),
                    generic_args: v.into_iter().map(|x| x.into_cpp()).collect(),
                }
            }
            RustType::Dyn(tr, marker_bounds) => {
                let tr_as_cpp_type = tr.into_cpp();
                CppType {
                    path: CppPath::from("rust::Dyn"),
                    generic_args: [tr_as_cpp_type]
                        .into_iter()
                        .chain(
                            marker_bounds
                                .iter()
                                .map(|x| CppType::from(&*format!("rust::{x}"))),
                        )
                        .collect(),
                }
            }
        }
    }
}

pub struct RustFile {
    pub hotreload: bool,
    pub text: String,
    pub panic_to_exception: bool,
    ind: usize,
}
impl RustFile {
    fn indentation(&self) -> String { "    ".repeat(self.ind) }
    fn indent_inc(&mut self) { self.ind += 1; }
    fn indent_dec(&mut self) { self.ind -= 1; }
}
impl Default for RustFile {
    fn default() -> Self {
        #[cfg(feature="hotreload")]
        let hotreload = true;
        #[cfg(not(feature="hotreload"))]
        let hotreload = false;

        Self {
            ind: 0,
            hotreload,
            text:
r#"#[allow(dead_code)] mod zngur_types {
    pub struct ZngurCppOpaqueBorrowedObject(());
    #[repr(C)] pub struct ZngurCppOpaqueOwnedObject {
        data: *mut u8,
        destructor: extern "C" fn(*mut u8),
    }
    impl ZngurCppOpaqueOwnedObject {
        pub unsafe fn new(data: *mut u8, destructor: extern "C" fn(*mut u8)) -> Self { Self { data, destructor } }
        pub fn ptr(&self) -> *mut u8 { self.data }
    }
    impl Drop for ZngurCppOpaqueOwnedObject { fn drop(&mut self) { (self.destructor)(self.data) } }
}
#[allow(unused_imports)] pub use zngur_types::ZngurCppOpaqueOwnedObject;
#[allow(unused_imports)] pub use zngur_types::ZngurCppOpaqueBorrowedObject;"#
            .to_owned(),
            panic_to_exception: false,
        }
    }
}

impl Write for RustFile {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.text.write_str(s)
    }
}

macro_rules! w {
    ($dst:expr, $($arg:tt)*) => {
        { let _ = write!($dst, $($arg)*); }
    };
}

macro_rules! wln {
    ($dst:expr, $($arg:tt)*) => {
        { let _ = writeln!($dst, $($arg)*); }
    };
}

fn mangle_name(name: &str) -> String {
    let mut name = "__zngur_"
        .chars()
        .chain(name.chars().filter(|c| !c.is_whitespace()))
        .chain(Some('_'))
        .collect::<String>();
    let bads = [
        (1, "::<", 'm'),
        (1, ">::", 'n'),
        (1, "->", 'a'),
        (2, "&", 'r'),
        (2, "=", 'e'),
        (2, "<", 'x'),
        (2, ">", 'y'),
        (2, "[", 'j'),
        (2, "]", 'k'),
        (2, "::", 's'),
        (2, ",", 'c'),
        (2, "+", 'l'),
        (2, "(", 'p'),
        (2, ")", 'q'),
    ];
    while let Some((pos, which)) = bads.iter().filter_map(|x| Some((name.find(x.1)?, x))).min() {
        name.replace_range(pos..pos + which.1.len(), "_");
        w!(name, "{}{pos}", which.2);
    }
    name
}

pub struct ConstructorMangledNames {
    pub constructor: String,
    pub match_check: String,
}

impl RustFile {
    fn call_cpp_function(&mut self, name: &str, first_input: Option<&str>, inputs: usize) {
        let ind = self.indentation();
        for n in 0..inputs {
            w!(self, "\n{ind}let mut i{n} = ::core::mem::MaybeUninit::new(i{n});")
        }
        w!(self, "\n{ind}let mut r = ::core::mem::MaybeUninit::uninit();");
        if self.hotreload {
            w!(self, "\n{ind}(GetZngurCApi().");
        }
        w!(self, "{name}");
        if self.hotreload {
            w!(self, ")");
        }
        w!(self, "(");
        if let Some(i) = first_input {
            w!(self, "{i}, ");
        }
        for n in 0..inputs {
            w!(self, "i{n}.as_mut_ptr() as *mut u8, ");
        }
        w!(self, "r.as_mut_ptr() as *mut u8);");
        w!(self, "\n{ind}r.assume_init()");
    }

    pub fn add_static_is_copy_assert(&mut self, ty: &RustType) {
        w!(self, r#"
const _: () = {{
    const fn static_assert_is_copy<T: Copy>() {{}}
    static_assert_is_copy::<{ty}>();
}};"#);
    }

    pub fn add_static_size_assert(&mut self, ty: &RustType, size: usize) {
        w!( self, r#"
const _: [(); {size}] = [(); ::std::mem::size_of::<{ty}>()];"#);
    }

    pub fn add_static_align_assert(&mut self, ty: &RustType, align: usize) {
        w!(self, r#"
const _: [(); {align}] = [(); ::std::mem::align_of::<{ty}>()];"#);
    }

    pub(crate) fn add_builder_for_dyn_trait(&mut self, tr: &ZngurTrait) -> CppTraitDefinition {
        assert!(matches!(tr.tr, RustTrait::Normal { .. }));
        let mut method_mangled_name = vec![];
        w!(self, r#"
extern "C" {{"#);
        for method in &tr.methods {
            let name = mangle_name(&tr.tr.to_string()) + "_" + &method.name;
            w!(self, r#"
    fn {name}(data: *mut u8, {} o: *mut u8);"#,
                method
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(n, _)| format!("i{n}: *mut u8,"))
                    .join(" "));
            method_mangled_name.push(name);
        }
        w!(self, "\n}}");
        let link_name = self.add_builder_for_dyn_trait_owned(tr, &method_mangled_name);
        let link_name_ref = self.add_builder_for_dyn_trait_borrowed(tr, &method_mangled_name);
        CppTraitDefinition::Normal {
            as_ty: tr.tr.into_cpp(),
            methods: tr
                .methods
                .clone()
                .into_iter()
                .zip(method_mangled_name)
                .map(|(x, rust_link_name)| CppTraitMethod {
                    name: x.name,
                    rust_link_name,
                    inputs: x.inputs.into_iter().map(|x| x.into_cpp()).collect(),
                    output: x.output.into_cpp(),
                })
                .collect(),
            link_name,
            link_name_ref,
        }
    }

    fn add_builder_for_dyn_trait_owned(
        &mut self,
        tr: &ZngurTrait,
        method_mangled_name: &[String],
    ) -> String {
        let trait_name = tr.tr.to_string();
        let (trait_without_assocs, assocs) = tr.tr.clone().take_assocs();
        let mangled_name = mangle_name(&trait_name);
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {mangled_name}(data: *mut u8, destructor: extern "C" fn(*mut u8), o: *mut u8) {{
    struct Wrapper {{ value: ZngurCppOpaqueOwnedObject }}
    impl {trait_without_assocs} for Wrapper {{
"#
        );
        for (name, ty) in assocs {
            w!(self, "\n        type {name} = {ty};");
        }
        for (method, rust_link_name) in tr.methods.iter().zip(method_mangled_name) {
            w!(self, "\n        fn {}(", method.name);
            match &method.receiver {
                crate::ZngurMethodReceiver::Static => {
                    panic!("traits with static methods are not object safe");
                }
                crate::ZngurMethodReceiver::Ref(Mutability::Not, None) => w!(self, "&self"),
                crate::ZngurMethodReceiver::Ref(Mutability::Not, Some(lt)) => w!(self, "&'{lt} cself"),
                crate::ZngurMethodReceiver::Ref(Mutability::Mut, None) => w!(self, "&mut self"),
                crate::ZngurMethodReceiver::Ref(Mutability::Mut, Some(lt)) => w!(self, "&'{lt} mut self"),
                crate::ZngurMethodReceiver::Move => w!(self, "self"),
            }
            for (i, ty) in method.inputs.iter().enumerate() {
                w!(self, ", i{i}: {ty}");
            }
            w!(self, ") -> {} {{ unsafe {{", method.output);
            self.indent_inc();
            self.indent_inc();
            self.indent_inc();
            let ind = self.indentation();
            w!(self, "\n{ind}let data = self.value.ptr();");
            self.call_cpp_function(&rust_link_name, Some("data"), method.inputs.len());
            self.indent_dec();
            let ind = self.indentation();
            w!(self, "\n{ind}}} }}");
            self.indent_dec();
            self.indent_dec();
        }
        w!(self, r#"
    }}
    unsafe {{ 
        let this = Wrapper {{ value: ZngurCppOpaqueOwnedObject::new(data, destructor) }};
        let r: Box<dyn {trait_name}> = Box::new(this);
        std::ptr::write(o as *mut _, r)
    }}
}}"#);
        mangled_name
    }

    fn add_builder_for_dyn_trait_borrowed(
        &mut self,
        tr: &ZngurTrait,
        method_mangled_name: &[String],
    ) -> String {
        let trait_name = tr.tr.to_string();
        let (trait_without_assocs, assocs) = tr.tr.clone().take_assocs();
        let mangled_name = mangle_name(&trait_name) + "_borrowed";
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {mangled_name}(data: *mut u8, o: *mut u8) {{
    struct Wrapper(ZngurCppOpaqueBorrowedObject);
    impl {trait_without_assocs} for Wrapper {{"#);
        for (name, ty) in assocs {
            w!(self, "\n        type {name} = {ty};");
        }
        for (method, rust_link_name) in tr.methods.iter().zip(method_mangled_name) {
            w!(self, "\n        fn {}(", method.name);
            match &method.receiver {
                crate::ZngurMethodReceiver::Static => {
                    panic!("traits with static methods are not object safe");
                }
                crate::ZngurMethodReceiver::Ref(Mutability::Not, None) => w!(self, "&self"),
                crate::ZngurMethodReceiver::Ref(Mutability::Not, Some(lt)) => w!(self, "&'{lt} self"),
                crate::ZngurMethodReceiver::Ref(Mutability::Mut, None) => w!(self, "&mut self"),
                crate::ZngurMethodReceiver::Ref(Mutability::Mut, Some(lt)) => w!(self, "&'{lt} mut self"),
                crate::ZngurMethodReceiver::Move => w!(self, "self"),
            }
            for (i, ty) in method.inputs.iter().enumerate() {
                w!(self, ", i{i}: {ty}");
            }
            w!(self, ") -> {} {{ unsafe {{", method.output);
            self.indent_inc();
            self.indent_inc();
            let ind = self.indentation();
            w!(self, "\n{ind}let data = ::std::mem::transmute::<_, *mut u8>(self);");
            self.call_cpp_function(&rust_link_name, Some("data"), method.inputs.len());
            self.indent_dec();
            let ind = self.indentation();
            w!(self, "\n{ind}}} }}");
            self.indent_dec();
        }
        w!(self, r#"
    }}
    unsafe {{ 
        let this = data as *mut Wrapper;
        let r: &dyn {trait_name} = &*this;
        std::ptr::write(o as *mut _, r)
    }}
}}"#);
        mangled_name
    }

    pub fn add_builder_for_dyn_fn(
        &mut self,
        name: &str,
        inputs: &[RustType],
        output: &RustType,
    ) -> String {
        let mangled_name = mangle_name(&inputs.iter().chain(Some(output)).join(", "));
        let trait_str = format!("{name}({}) -> {output}", inputs.iter().join(", "));
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {mangled_name}(data: *mut u8, destructor: extern "C" fn(*mut u8), call: extern "C" fn(data: *mut u8, {} o: *mut u8), o: *mut u8) {{
    let this = unsafe {{ ZngurCppOpaqueOwnedObject::new(data, destructor) }};
    let r: Box<dyn {trait_str}> = Box::new(move |{}| unsafe {{
        _ = &this;
        let data = this.ptr();"#,
            inputs
                .iter()
                .enumerate()
                .map(|(n, _)| format!("i{n}: *mut u8, "))
                .join(" "),
            inputs
                .iter()
                .enumerate()
                .map(|(n, ty)| format!("i{n}: {ty}"))
                .join(", "),
        );
        self.indent_inc();
        self.indent_inc();
        self.call_cpp_function("call", Some("data"), inputs.len());
        self.indent_dec();
        self.indent_dec();
        w!(self, r#"
    }});
    unsafe {{ std::ptr::write(o as *mut _, r) }}
}}"#);
        mangled_name
    }

    pub fn add_tuple_constructor(&mut self, fields: &[RustType]) -> String {
        let constructor = mangle_name(&fields.iter().join("&"));
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {constructor}("#);
        for name in 0..fields.len() {
            w!(self, "f_{name}: *mut u8, ");
        }
        w!(self, r#"o: *mut u8) {{ unsafe {{ ::std::ptr::write(o as *mut _, ("#);
        for (name, ty) in fields.iter().enumerate() {
            w!(self, "::std::ptr::read(f_{name} as *mut {ty}), ");
        }
        w!(self, ")) }} }}");
        constructor
    }

    pub fn add_constructor(
        &mut self,
        rust_name: &str,
        args: &[(String, RustType)],
        rust_value: Option<&(String, String)>,
    ) -> ConstructorMangledNames {
        let constructor = mangle_name(rust_name);
        let match_check = format!("{constructor}_check");
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {constructor}("#);
        for (name, _) in args {
            w!(self, "f_{name}: *mut u8, ");
        }
        w!(self, r#"o: *mut u8) {{ unsafe {{ ::std::ptr::write(o as *mut _, {rust_name} {{ "#);
        for (name, ty) in args {
            w!(self, "{name}: ::std::ptr::read(f_{name} as *mut {ty}), ");
        }
        if let Some((name, expr)) = rust_value {
            w!(self, "{name}: {expr}, ");
        }
        w!(self, "}}) }} }}");
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {match_check}(i: *mut u8, o: *mut u8) {{ unsafe {{ *o = matches!(&*(i as *mut &_), {rust_name} {{ .. }}) as u8; }} }}"#);
        ConstructorMangledNames {
            constructor,
            match_check,
        }
    }

    pub fn add_extern_cpp_impl(
        &mut self,
        owner: &RustType,
        tr: Option<&RustTrait>,
        methods: &[ZngurMethod],
        lifetimes: &[String],
    ) -> Vec<String> {
        let mut mangled_names = vec![];
        w!(self, r#"
extern "C" {{"#);
        for method in methods {
            let mn = mangle_name(&format!("{}_extern_method_{}", owner, method.name));
            w!(
                self,
                r#"
    fn {mn}("#
            );
            let input_offset = if method.receiver == ZngurMethodReceiver::Static { 0 } else { 1 };
            for n in 0..method.inputs.len() + input_offset {
                w!(self, "i{n}: *mut u8, ");
            }
            w!(self, r#"o: *mut u8);"#);
            mangled_names.push(mn);
        }
        w!(self, "\n}}");
        match tr {
            Some(tr) => {
                let impl_lts = lifetimes.iter().map(|lt| format!("'{lt}")).collect::<Vec<_>>().join(", ");
                let owner_lts = match owner {
                    RustType::Adt(RustPathAndGenerics { lifetimes, .. }) =>
                        lifetimes.iter().map(|lt| format!("'{lt}")).collect::<Vec<_>>().join(", "),
                    _ => "".to_string(),
                };
                let (tr, assocs) = tr.clone().take_assocs();
                w!(self, r#"
impl{impl_lts} {tr} for {owner}{owner_lts} {{"#,
                    impl_lts = if impl_lts.is_empty() { impl_lts } else { format!("<{impl_lts}>") },
                    owner_lts = if owner_lts.is_empty() { owner_lts } else { format!("<{owner_lts}>") },
                );
                for (name, ty) in assocs {
                    w!(self, r#"
    type {name} = {ty};"#);
                }
            }
            None => w!(self, r#"
impl {owner} {{"#),
        }
        for (mn, method) in mangled_names.iter().zip(methods) {
            if tr.is_none() {
                w!(self, "\n    pub ");
            }
            w!(self, r#"fn {}("#, method.name);
            match &method.receiver {
                ZngurMethodReceiver::Static => (),
                ZngurMethodReceiver::Ref(Mutability::Mut, None) => w!(self, "&mut self, "),
                ZngurMethodReceiver::Ref(Mutability::Mut, Some(lt)) => w!(self, "&'{lt} mut self, "),
                ZngurMethodReceiver::Ref(Mutability::Not, None) => w!(self, "&self, "),
                ZngurMethodReceiver::Ref(Mutability::Not, Some(lt)) => w!(self, "&'{lt} self, "),
                ZngurMethodReceiver::Move => w!(self, "self, "),
            }
            let input_offset = if method.receiver == ZngurMethodReceiver::Static {
                0
            } else {
                1
            };
            for (ty, n) in method.inputs.iter().zip(input_offset..) {
                w!(self, "i{n}: {ty}, ");
            }
            w!(self, ") -> {} {{ unsafe {{", method.output);
            self.indent_inc();
            self.indent_inc();
            if method.receiver != ZngurMethodReceiver::Static {
                w!(self, "\n        let i0 = self;");
            }
            self.call_cpp_function(mn, None, method.inputs.len() + input_offset);
            self.indent_dec();
            self.indent_dec();
            w!(self, "\n    }} }} ");
        }
        w!(self, "\n}}");
        mangled_names
    }

    pub fn add_extern_cpp_function(
        &mut self,
        rust_name: &str,
        inputs: &[RustType],
        output: &RustType,
    ) -> String {
        let mangled_name = mangle_name(rust_name);
        w!(self,
r#"extern "C" {{ fn {mangled_name}("#
        );
        for (n, _) in inputs.iter().enumerate() {
            w!(self, "i{n}: *mut u8, ");
        }
        w!(self, r#"o: *mut u8); }}"#);
        w!(self, r#"
pub(crate) fn {rust_name}("#
        );
        for (n, ty) in inputs.iter().enumerate() {
            w!(self, "i{n}: {ty}, ");
        }
        w!(self, ") -> {output} {{ unsafe {{");
        self.indent_inc();
        self.call_cpp_function(&mangled_name, None, inputs.len());
        self.indent_dec();
        w!(self, "\n}} }}");
        mangled_name
    }

    pub fn add_cpp_value_bridge(&mut self, ty: &RustType, field: &str) -> String {
        let mangled_name = mangle_name(&format!("{ty}_cpp_value_{field}"));
        w!(self, r#"
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn {mangled_name}(d: *mut u8) -> *mut ZngurCppOpaqueOwnedObject {{ unsafe {{ &mut (*(d as *mut {ty})).{field} }} }}"#);
        mangled_name
    }

    pub fn add_function(
        &mut self,
        rust_name: &str,
        inputs: &[RustType],
        output: &RustType,
        use_path: Option<Vec<String>>,
        deref: bool,
    ) -> String {
        let mangle = if self.hotreload { "" } else { "#[no_mangle]\n" };
        let public = if self.hotreload { "" } else { "pub " };
        let mut mangled_name = mangle_name(rust_name);
        if deref {
            mangled_name += "_deref_";
            mangled_name += &mangle_name(&inputs[0].to_string());
        }
        w!(self, r#"
#[allow(non_snake_case)] {mangle}{public}extern "C" fn {mangled_name}"#);

        let mut signature = "(".to_string();
        for n in 0..inputs.len() {
            signature += &format!("i{n}: *mut u8, ");
        }
        signature += "o: *mut u8)";

        wln!(self, "{signature} {{ unsafe {{");
        self.wrap_in_catch_unwind(|this| {
            if let Some(use_path) = use_path {
                if use_path.first().is_some_and(|x| x == "crate") {
                    wln!(this, "    use {};", use_path.iter().join("::"));
                } else {
                    wln!(this, "    use ::{};", use_path.iter().join("::"));
                }
            }
            w!(
                this,
                "    ::std::ptr::write(o as *mut {output}, {rust_name}("
            );
            if deref {
                w!(this, "&");
            }
            for (n, ty) in inputs.iter().enumerate() {
                w!(this, "::std::ptr::read(i{n} as *mut {ty}), ");
            }
            w!(this, "));");
        });
        w!(self, "\n}} }}");
        mangled_name
    }

    pub(crate) fn add_wellknown_trait(
        &mut self,
        ty: &RustType,
        wellknown_trait: ZngurWellknownTrait,
    ) -> ZngurWellknownTraitData {
        let mangle = if self.hotreload { "" } else { "#[no_mangle]\n" };
        let public = if self.hotreload { "" } else { "pub " };
        match wellknown_trait {
            ZngurWellknownTrait::Unsized => ZngurWellknownTraitData::Unsized,
            ZngurWellknownTrait::Copy => ZngurWellknownTraitData::Copy,
            ZngurWellknownTrait::Drop => {
                let drop_in_place = mangle_name(&format!("{ty}=drop_in_place"));
                w!(self, r#"
#[allow(non_snake_case)] {mangle}{public}extern "C" fn {drop_in_place}(v: *mut u8) {{ unsafe {{ ::std::ptr::drop_in_place(v as *mut {ty}); }} }}"#);
                ZngurWellknownTraitData::Drop { drop_in_place }
            }
            ZngurWellknownTrait::Debug => {
                let pretty_print = mangle_name(&format!("{ty}=debug_pretty"));
                let debug_print = mangle_name(&format!("{ty}=debug_print"));
                wln!(self, r#"
#[allow(non_snake_case)] {mangle}{public}extern "C" fn {pretty_print}(v: *mut u8) {{ eprintln!("{{:#?}}", unsafe {{ &*(v as *mut {ty}) }}); }}"#);
                wln!(self, r#"
#[allow(non_snake_case)] {mangle}{public}extern "C" fn {debug_print}(v: *mut u8) {{ eprintln!("{{:?}}", unsafe {{ &*(v as *mut {ty}) }}); }}"#);
                ZngurWellknownTraitData::Debug {
                    pretty_print,
                    debug_print,
                }
            }
        }
    }

    pub(crate) fn enable_panic_to_exception(&mut self) {
        wln!(
            self,
            r#"thread_local! {{
            pub static PANIC_PAYLOAD: ::std::cell::Cell<Option<()>> = ::std::cell::Cell::new(None);
        }}
        #[allow(non_snake_case)] #[no_mangle] pub fn __zngur_detect_panic() -> u8 {{
            PANIC_PAYLOAD.with(|p| {{
                let pp = p.take();
                let r = if pp.is_some() {{ 1 }} else {{ 0 }};
                p.set(pp);
                r
            }})
        }}
        #[allow(non_snake_case)] #[no_mangle] pub fn __zngur_take_panic() {{ PANIC_PAYLOAD.with(|p| {{ p.take(); }}) }}"#);
        self.panic_to_exception = true;
    }

    fn wrap_in_catch_unwind(&mut self, f: impl FnOnce(&mut RustFile)) {
        if !self.panic_to_exception {
            f(self);
        } else {
            wln!(self, "let e = ::std::panic::catch_unwind(|| {{");
            f(self);
            wln!(self, "}});");
            wln!(
                self,
                "if let Err(_) = e {{ PANIC_PAYLOAD.with(|p| p.set(Some(()))) }}"
            );
        }
    }

    pub(crate) fn add_layout_policy_shim(
        &mut self,
        ty: &RustType,
        layout: LayoutPolicy,
    ) -> CppLayoutPolicy {
        match layout {
            LayoutPolicy::StackAllocated { size, align } => {
                CppLayoutPolicy::StackAllocated { size, align }
            }
            LayoutPolicy::HeapAllocated => {
                let size_fn = mangle_name(&format!("{ty}_size_fn"));
                let alloc_fn = mangle_name(&format!("{ty}_alloc_fn"));
                let free_fn = mangle_name(&format!("{ty}_free_fn"));
                w!(self, r#"
                #[allow(non_snake_case)] #[no_mangle] pub fn {size_fn}() -> usize {{ ::std::mem::size_of::<{ty}>() }}
                #[allow(non_snake_case)] #[no_mangle] pub fn {alloc_fn}() -> *mut u8 {{ unsafe {{ ::std::alloc::alloc(::std::alloc::Layout::new::<{ty}>()) }} }}
                #[allow(non_snake_case)] #[no_mangle] pub fn {free_fn}(p: *mut u8) {{ unsafe {{ ::std::alloc::dealloc(p, ::std::alloc::Layout::new::<{ty}>()) }} }}"#);
                CppLayoutPolicy::HeapAllocated {
                    size_fn,
                    alloc_fn,
                    free_fn,
                }
            }
            LayoutPolicy::OnlyByRef => CppLayoutPolicy::OnlyByRef,
        }
    }

    #[cfg(feature="hotreload")]
    pub fn add_hotload_api(&mut self, cpp_file: &crate::CppFile) {
        use crate::cpp::EmitMode;

        w!(self, r#"
#[allow(non_snake_case)] #[repr(C)] pub struct ZngurRsApi {{"#);
        if cpp_file.fn_defs.is_empty() && cpp_file.type_defs.is_empty() && cpp_file.trait_defs.is_empty() {
            w!(self, "\n    _unused: u32");
        } else {
            for f in &cpp_file.fn_defs {
                f.sig.emit_link_decl(&mut EmitMode::Rust(self)).expect("failed to emit link decl");
            }
            for td in &cpp_file.type_defs {
                td.emit_links(&mut EmitMode::Rust(self)).expect("failed to emit links");
            }
            for (_, td) in &cpp_file.trait_defs {
                td.emit_links(&mut EmitMode::Rust(self)).expect("failed to emit links");
            }
        }
        w!(self, r#"
}}
#[allow(non_snake_case)] #[repr(C)] pub struct ZngurCApi {{"#);
        if cpp_file.exported_fn_defs.is_empty() && cpp_file.exported_impls.is_empty() {
            w!(self, "\n    _unused: u32");
        } else {
            for func in &cpp_file.exported_fn_defs {
                w!(self, r#"
    pub {}: extern "C" fn ("#, func.sig.rust_link_name);
                for n in 0..func.sig.inputs.len() {
                    w!(self, "i{n}: *mut u8, ");
                }
                w!(self, "o: *mut u8),");
            }
            (&cpp_file.exported_impls).into_iter().for_each(|imp| {
                for (_, sig) in &imp.methods {
                    w!(self, r#"
    pub {}: extern "C" fn ("#, sig.rust_link_name);
                    for n in 0..sig.inputs.len() {
                        w!(self, "i{n}: *mut u8, ");
                    }
                    w!(self, "o: *mut u8),");
                }
            });
            for defs in cpp_file.trait_defs.values() {
                match defs {
                    CppTraitDefinition::Fn { sig } => {
                        w!(self, r#"
    pub {}: extern "C" fn(data: *mut u8, "#, sig.rust_link_name);
                        for n in 0..sig.inputs.len() {
                            w!(self, "i{n}: *mut u8, ");
                        }
                        w!(self, "o: *mut u8),");
                    }
                    CppTraitDefinition::Normal { methods, .. } => {
                        for method in methods {
                            w!(self, r#"
    pub {}: extern "C" fn(data: *mut u8, "#, method.rust_link_name);
                            for n in 0..method.inputs.len() {
                                w!(self, "i{n}: *mut u8, ");
                            }
                            w!(self, "o: *mut u8),");
                        }
                    }
                }
            }
        }
        w!(self, r#"
}}
static CAPI: std::sync::OnceLock<ZngurCApi> = std::sync::OnceLock::new();
#[allow(dead_code)] #[allow(non_snake_case)] fn GetZngurCApi() -> &'static ZngurCApi {{ CAPI.get().expect("zngur capi not initialized") }}
#[allow(non_snake_case)] #[no_mangle] pub extern "C" fn GetZngurRsApi(capi: ZngurCApi) -> ZngurRsApi {{
    CAPI.get_or_init(|| capi);
    ZngurRsApi {{"#);
        if cpp_file.fn_defs.is_empty() && cpp_file.type_defs.is_empty() && cpp_file.trait_defs.is_empty() {
            w!(self, "\n        _unused: 0");
        } else {
            for f in &cpp_file.fn_defs {
                f.sig.emit_link_decl(&mut EmitMode::RustLinkNameOnly(self)).expect("failed to emit link decl name");
            }
            for td in &cpp_file.type_defs {
                td.emit_links(&mut EmitMode::RustLinkNameOnly(self)).expect("failed to emit link names");
            }
            for (_, td) in &cpp_file.trait_defs {
                td.emit_links(&mut EmitMode::RustLinkNameOnly(self)).expect("failed to emit link names");
            }
        }
        w!(self, r#"
    }}
}}"#
        );
    
    }
}
