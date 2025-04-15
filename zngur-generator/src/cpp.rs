use std::{
    collections::HashMap, fmt::{Display, Write}, iter, sync::atomic::{AtomicBool, Ordering}
};

use itertools::Itertools;
use zngur_def::{Mutability, RustTrait, RustType, ZngurMethodReceiver};

use crate::{rust::IntoCpp, ZngurWellknownTraitData};

static SIG_OUTPUT: AtomicBool = AtomicBool::new(false);

#[derive(Debug)]
pub struct CppPath(pub Vec<String>);

impl CppPath {
    fn namespace(&self) -> &[String] {
        self.0.split_last().unwrap().1
    }

    fn emit_in_namespace(
        &self,
        state: &mut State,
        f: impl FnOnce(&mut State) -> std::fmt::Result,
    ) -> std::fmt::Result {
        for (n, p) in self.namespace().iter().enumerate() {
            if n == 0 {
                write!(state, "\n")?;
            }
            #[cfg(feature = "std-namespace-fix")]
            if p == "std" {
                write!(state, "namespace {}_ {{ ", p)?;
            } else {
                write!(state, "namespace {} {{ ", p)?;
            }
            #[cfg(not(feature = "std-namespace-fix"))]
            write!(state, "namespace {} {{ ", p)?;
        }
        state.ident_inc();
        f(state)?;
        state.ident_dec();
        for n in 0..self.namespace().len() {
            if !state.disable_ending_newline && n == 0 {
                write!(state, "\n")?;
            }
            write!(state, "}} ")?;
        }
        Ok(())
    }

    fn name(&self) -> &str {
        self.0.split_last().unwrap().0
    }

    fn is_unit(&self) -> bool {
        self.0 == ["rust", "Unit"]
    }

    fn need_header(&self) -> bool {
        self.0.first().map(|x| x.as_str()) == Some("rust")
            && self.0 != ["rust", "Unit"]
            && self.0 != ["rust", "Ref"]
            && self.0 != ["rust", "RefMut"]
    }

    pub(crate) fn from_rust_path(path: &[String]) -> CppPath {
        CppPath(
            iter::once("rust")
                .chain(path.iter().map(|x| x.as_str()))
                .map(cpp_handle_keyword)
                .map(|x| x.to_owned())
                .collect(),
        )
    }
}

impl<const N: usize> From<[&str; N]> for CppPath {
    fn from(value: [&str; N]) -> Self {
        CppPath(value.iter().map(|x| x.to_string()).collect())
    }
}

impl From<&str> for CppPath {
    fn from(value: &str) -> Self {
        let value = value.trim();
        CppPath(value.split("::").map(|x| x.to_owned()).collect())
    }
}

impl Display for CppPath {
    #[cfg(not(feature = "std-namespace-fix"))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !SIG_OUTPUT.load(Ordering::SeqCst) { write!(f, "::")?; }
        write!(f, "{}", self.0.iter().join("::"))
    }
    #[cfg(feature = "std-namespace-fix")]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !SIG_OUTPUT.load(Ordering::SeqCst) { write!(f, "::")?; }
        write!(f, "{}", self.0.iter().map(|s| if s == "std" { "std_" } else { s }).join("::"))
    }
}

#[derive(Debug)]
pub struct CppType {
    pub path: CppPath,
    pub generic_args: Vec<CppType>,
    pub is_enum: bool,
}

impl CppType {
    pub fn into_ref(self) -> CppType {
        CppType {
            path: CppPath::from("rust::Ref"),
            generic_args: vec![self],
            is_enum: false,
        }
    }

    pub fn is_void(&self) -> bool {
        self.path.is_unit() && self.generic_args.is_empty() && !self.is_enum
    }

    fn emit_specialization_decl(&self, state: &mut State) -> std::fmt::Result {
        if self.generic_args.is_empty() {
            write!(state, r"
    struct {}", self.path.name())?;
        } else {
            write!(state,
                r"
    template<> struct {}<{}>",
                self.path.name(),
                self.generic_args.iter().join(", ")
            )?;
        }
        Ok(())
    }

    fn emit_header(&self, state: &mut State) -> std::fmt::Result {
        for x in &self.generic_args {
            x.emit_header(state)?;
        }
        if !self.path.need_header() {
            return Ok(());
        }
        state.disable_ending_newline = true;
        let ret = self.path.emit_in_namespace(state, |state| {
            if !self.generic_args.is_empty() {
                write!(state, "template<typename ...T> ")?;
            }
            write!(state, "struct {}; ", self.path.name())
        });
        state.disable_ending_newline = false;
        ret
    }
}

impl Display for CppType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path)?;
        if !self.generic_args.is_empty() {
            write!(f, "<{}>", self.generic_args.iter().join(", "))?;
        }
        Ok(())
    }
}

fn split_string(input: &str) -> impl Iterator<Item = String> {
    let mut parts = Vec::new();
    let mut current_part = String::new();
    let mut parentheses_count = 0;

    for c in input.chars() {
        match c {
            ',' if parentheses_count == 0 => {
                parts.push(current_part.clone());
                current_part.clear();
            }
            '<' => {
                parentheses_count += 1;
                current_part.push(c);
            }
            '>' => {
                parentheses_count -= 1;
                current_part.push(c);
            }
            _ => {
                current_part.push(c);
            }
        }
    }

    if !current_part.is_empty() {
        parts.push(current_part);
    }

    parts.into_iter()
}

impl From<&str> for CppType {
    fn from(value: &str) -> Self {
        let value = value.trim();
        match value.split_once('<') {
            None => CppType {
                path: CppPath::from(value),
                generic_args: vec![],
                is_enum: false,
            },
            Some((path, generics)) => {
                let generics = generics.strip_suffix('>').unwrap();
                CppType {
                    path: CppPath::from(path),
                    generic_args: split_string(generics).map(|x| CppType::from(&*x)).collect(),
                    is_enum: false,
                }
            }
        }
    }
}

pub struct State {
    text: String,
    panic_to_exception: bool,
    hotreload: bool,
    indent_count: usize,
    disable_ending_newline: bool,
}

impl State {
    fn panic_handler(&self) -> String {
        if self.panic_to_exception {
            r#"
    if (__zngur_detect_panic()) {
        __zngur_take_panic();
        throw ::rust::Panic{};
    }"#.to_owned()
        } else {
            "".to_owned()
        }
    }
    fn ident_inc(&mut self) { self.indent_count += 1; }
    fn ident_dec(&mut self) { self.indent_count -= 1; }
    fn indent(&self) -> String {
        "    ".repeat(self.indent_count)
    }
}

impl Write for State {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.text += s;
        Ok(())
    }
}

#[derive(Debug)]
pub struct CppTraitMethod {
    pub name: String,
    pub rust_link_name: String,
    pub inputs: Vec<CppType>,
    pub output: CppType,
}

pub enum EmitMode<'a, W> where W: Write {
    Cpp(&'a mut W, bool),
    Rust(&'a mut W),
    RustLinkNameOnly(&'a mut W),
}
impl<'a, W> EmitMode<'a, W> where W: Write {
    pub fn hotreload(&self) -> bool {
        match self {
            EmitMode::Cpp(_, hotreload) => *hotreload,
            _ => true,
        }
    }
}
impl<'a, W> Write for EmitMode<'a, W> where W: Write {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        match self {
            EmitMode::Cpp(m, _) |
            EmitMode::Rust(m) |
            EmitMode::RustLinkNameOnly(m) => write!(m, "{s}"),
        }
    }
}

#[derive(Debug)]
pub struct CppFnSig {
    pub rust_link_name: String,
    pub inputs: Vec<CppType>,
    pub output: CppType,
}

impl CppFnSig {
    fn emit_params(&self, state: &mut EmitMode<impl Write>) -> std::fmt::Result {
        match state {
            EmitMode::Cpp(state, _) => {
                for n in 0..self.inputs.len() {
                    write!(state, "uint8_t* i{n}, ")?;
                }
                write!(state, "uint8_t* o")?;
            }
            EmitMode::Rust(state) => {
                for n in 0..self.inputs.len() {
                    write!(state, "i{n}: *mut u8, ")?;
                }
                write!(state, "o: *mut u8")?;
            }
            EmitMode::RustLinkNameOnly(_) => (),
        }
        Ok(())
    }
    fn emit_link(&self, state: &mut EmitMode<impl Write>, is_rust_link_decl: bool) -> std::fmt::Result {
        match state {
            EmitMode::Cpp(state, hotreload) => {
                if *hotreload && is_rust_link_decl {
                    write!(state, "    void (*{})(", self.rust_link_name)?;
                } else {
                    write!(state, "void {}(", self.rust_link_name)?;
                }
                self.emit_params(&mut EmitMode::Cpp(*state, *hotreload))?;
                write!(state, ")")?;
            }
            EmitMode::Rust(state) => {
                write!(state, "\n    pub {}: extern \"C\" fn(", self.rust_link_name)?;
                self.emit_params(&mut EmitMode::Rust(*state))?;
                write!(state, ")")?;
            }
            EmitMode::RustLinkNameOnly(state) => {
                write!(state, "\n        {}", self.rust_link_name)?;
            }
        }
        Ok(())
    }
    pub fn emit_link_decl(&self, state: &mut EmitMode<impl Write>) -> std::fmt::Result {
        self.emit_link(state, true)?;
        match state {
            EmitMode::Cpp(..) => writeln!(state, ";"),
            EmitMode::Rust(_) => write!(state, ","),
            EmitMode::RustLinkNameOnly(_) => write!(state, ","),
        }
    }

    fn emit_cpp_header(&self, state: &mut State, fn_name: &str) -> std::fmt::Result {
        let CppFnSig {
            inputs,
            output,
            rust_link_name: _,
        } = self;
        write!(
            state,
            "{output} {fn_name}({input_defs});",
            input_defs = inputs
                .iter()
                .enumerate()
                .map(|(n, ty)| format!("{ty} i{n}"))
                .join(", "),
        )
    }

    fn emit_cpp_def(&self, state: &mut State, fn_name: &str) -> std::fmt::Result {
        let api = if state.hotreload { "GetZngurRsApi()." } else { "" };
        let ii = state.indent();
        let CppFnSig {
            inputs,
            output,
            rust_link_name,
        } = self;
        write!(state, r#"
{ii}inline {output} {fn_name}({input_defs}) {{
{ii}    {output} o = {{}};{deinits}
{ii}    {api}{rust_link_name}({input_args}::rust::__zngur_internal_data_ptr(o));{panic_handler}
{ii}    ::rust::__zngur_internal_assume_init(o);
{ii}    return o;
{ii}}}"#,
            input_defs = inputs
                .iter()
                .enumerate()
                .map(|(n, ty)| format!("{ty} i{n}"))
                .join(", "),
            input_args = (0..inputs.len())
                .map(|n| format!("::rust::__zngur_internal_data_ptr(i{n}), ")).join(""),
            panic_handler = state.panic_handler(),
            deinits = (0..inputs.len()).map(|n| format!(r#"
{ii}    ::rust::__zngur_internal_assume_deinit(i{n});"#)).join(""),
        )
    }
}

pub struct CppFnDefinition {
    pub name: CppPath,
    pub sig: CppFnSig,
}

pub struct CppExportedFnDefinition {
    pub name: String,
    pub sig: CppFnSig,
}

pub struct CppExportedImplDefinition {
    pub tr: Option<CppType>,
    pub ty: CppType,
    pub methods: Vec<(String, CppFnSig)>,
}

impl CppFnDefinition {
    fn emit_cpp_def(&self, state: &mut State) -> std::fmt::Result {
        self.name.emit_in_namespace(state, |state| {
            self.sig.emit_cpp_def(state, self.name.name())
        })
    }
}

pub struct CppMethod {
    pub name: String,
    pub kind: ZngurMethodReceiver,
    pub sig: CppFnSig,
}

#[derive(Debug)]
pub struct BuildFromFunction {
    pub sig: CppFnSig,
}

#[derive(Debug)]
pub enum CppTraitDefinition {
    Fn {
        sig: CppFnSig,
    },
    Normal {
        as_ty: CppType,
        methods: Vec<CppTraitMethod>,
        link_name: String,
        link_name_ref: String,
    },
}

impl CppTraitDefinition {
    pub fn emit_links(&self, state: &mut EmitMode<impl Write>) -> std::fmt::Result {
        match self {
            CppTraitDefinition::Fn {
                sig:
                    CppFnSig {
                        rust_link_name,
                        inputs,
                        output: _,
                    },
            } => {
                match state {
                    EmitMode::Cpp(_, hotreload) => {
                        if *hotreload {
                            writeln!(state, "    void (*{rust_link_name})(uint8_t* data, void(*destructor)(uint8_t *), void(*call)(uint8_t *, {} uint8_t *), uint8_t* o);",
                                (0..inputs.len()).map(|_| "uint8_t *, ").join(" "))?;
                        } else {
                            writeln!(state, "void {rust_link_name}(uint8_t* data, void(*destructor)(uint8_t *), void(*call)(uint8_t *, {} uint8_t *), uint8_t* o);",
                                (0..inputs.len()).map(|_| "uint8_t *, ").join(" "))?;
                        }
                    }
                    EmitMode::Rust(_) =>
                        write!(state, "\n    pub {rust_link_name}: extern \"C\" fn(data: *mut u8, destructor: extern \"C\" fn(*mut u8), call: extern \"C\" fn(*mut u8, {} *mut u8), o: *mut u8),",
                            (0..inputs.len()).map(|_| "*mut u8, ").join(" "))?,
                    EmitMode::RustLinkNameOnly(_) => write!(state, "\n        {rust_link_name},")?,
                }
            }
            CppTraitDefinition::Normal {
                link_name,
                link_name_ref,
                ..
            } => {
                match state {
                    EmitMode::Cpp(_, hotreload) => {
                        if *hotreload {
                            writeln!(state, "    void (*{link_name})(uint8_t *data, void destructor(uint8_t *), uint8_t *o);")?;
                            writeln!(state, "    void (*{link_name_ref})(uint8_t *data, uint8_t *o);")?;
                        } else {
                            writeln!(state, "void {link_name}(uint8_t *data, void destructor(uint8_t *), uint8_t *o);")?;
                            writeln!(state, "void {link_name_ref}(uint8_t *data, uint8_t *o);")?;
                        }
                    }
                    EmitMode::Rust(_) => {
                        write!(state, "\n    pub {link_name}: extern \"C\" fn(data: *mut u8, destructor: extern \"C\" fn(*mut u8), o: *mut u8),")?;
                        write!(state, "\n    pub {link_name_ref}: extern \"C\" fn(data: *mut u8, o: *mut u8),")?;
                    }
                    EmitMode::RustLinkNameOnly(_) => {
                        write!(state, "\n        {link_name},")?;
                        write!(state, "\n        {link_name_ref},")?;
                    },
                }
            }
        }
        Ok(())
    }

    fn emit(&self, state: &mut State) -> std::fmt::Result {
        let CppTraitDefinition::Normal {
            as_ty,
            methods,
            link_name: _,
            link_name_ref: _,
        } = self
        else {
            return Ok(());
        };

        as_ty.path.emit_in_namespace(state, |state| {
            as_ty.emit_specialization_decl(state)?;
            write!(
                state,
                r#"{{
    public:
        virtual ~{}() {{}}"#,
                as_ty.path.name(),
            )?;
            for method in methods {
                write!(
                    state,
                    r#"
        virtual {output} {name}({input}) = 0;"#,
                    output = method.output,
                    name = method.name,
                    input = method.inputs.iter().enumerate().map(|(n, x)| format!("{x} i{n}")).join(", "),
                )?;
            }
            write!(
                state,
                r#"
    }};"#,
            )
        })
    }

    fn emit_cpp(&self, state: &mut State) -> std::fmt::Result {
        match self {
            CppTraitDefinition::Fn { .. } => (),
            CppTraitDefinition::Normal {
                as_ty,
                methods,
                link_name: _,
                link_name_ref: _,
            } => {
                for method in methods {
                    write!(state, "void {}(uint8_t* data", method.rust_link_name)?;
                    for arg in 0..method.inputs.len() {
                        write!(state, ", uint8_t* i{arg}")?;
                    }
                    writeln!(state, ", uint8_t* o) {{")?;
                    writeln!(
                        state,
                        "   {as_ty}* data_typed = reinterpret_cast<{as_ty}*>(data);"
                    )?;
                    write!(
                        state,
                        "   {} oo = data_typed->{}({});",
                        method.output,
                        method.name,
                        method
                            .inputs
                            .iter()
                            .enumerate()
                            .map(|(n, ty)| {
                                format!("::rust::__zngur_internal_move_from_rust<{ty}>(i{n})")
                            })
                            .join(", ")
                    )?;
                    writeln!(state, "   ::rust::__zngur_internal_move_to_rust(o, oo);")?;
                    writeln!(state, "}}")?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CppLayoutPolicy {
    StackAllocated {
        size: usize,
        align: usize,
    },
    HeapAllocated {
        size_fn: String,
        alloc_fn: String,
        free_fn: String,
    },
    OnlyByRef,
}

pub struct CppTypeDefinition {
    pub ty: CppType,
    pub layout: CppLayoutPolicy,
    pub methods: Vec<CppMethod>,
    pub constructors: Vec<CppFnSig>,
    pub from_trait: Option<RustTrait>,
    pub from_trait_ref: Option<RustTrait>,
    pub wellknown_traits: Vec<ZngurWellknownTraitData>,
    pub alternates: Vec<String>,
    pub cpp_value: Option<(String, String)>,
    pub cpp_ref: Option<String>,
    pub alias: Option<RustType>,
}

impl Default for CppTypeDefinition {
    fn default() -> Self {
        Self {
            ty: CppType::from("fill::me::you::forgot::it"),
            layout: CppLayoutPolicy::OnlyByRef,
            methods: vec![],
            constructors: vec![],
            wellknown_traits: vec![],
            alternates: vec![],
            from_trait: None,
            from_trait_ref: None,
            cpp_value: None,
            cpp_ref: None,
            alias: None,
        }
    }
}

impl CppTypeDefinition {
    fn emit_ref_specialization(&self, state: &mut State) -> std::fmt::Result {
        for ref_kind in ["RefMut", "Ref"] {
            let is_unsized = self
                .wellknown_traits
                .contains(&ZngurWellknownTraitData::Unsized);
            if is_unsized {
                write!(state, r#"
namespace rust {{
    template<> struct {ref_kind}<{ty}> {{
        {ref_kind}() {{ data = {{0, 0}}; }}
    private:
        ::std::array<size_t, 2> data;
        friend uint8_t* ::rust::__zngur_internal_data_ptr<::rust::{ref_kind}<{ty}>>(const ::rust::{ref_kind}<{ty}>& t);"#,
                    ty = self.ty,
                )?;
            } else {
                write!(state, r#"
namespace rust {{
    template<> struct {ref_kind}<{ty}> {{
        {ref_kind}() {{ data = 0; }}
        {ref_kind}(const {ty}& t) {{ ::rust::__zngur_internal_check_init<{ty}>(t); data = reinterpret_cast<size_t>(__zngur_internal_data_ptr(t)); }}
    private:
        size_t data;
        friend uint8_t* ::rust::__zngur_internal_data_ptr<::rust::{ref_kind}<{ty}>>(const ::rust::{ref_kind}<{ty}>& t);"#,
                    ty = self.ty,
                )?;
            }
            write!(state, "\n    public:")?;
            if ref_kind == "Ref" {
                write!(state, r#"
        Ref(RefMut<{ty}> rm) {{ data = rm.data; }}"#, ty = self.ty)?;
            } else {
                write!(state, r#"
        friend Ref<{ty}>;"#, ty = self.ty)?;
            }

            match &self.from_trait_ref {
                Some(RustTrait::Fn { inputs, output, .. }) => {
                    let as_std_function = format!(
                        "::std::function<{}({})>",
                        output.into_cpp(),
                        inputs.iter().map(|x| x.into_cpp()).join(", ")
                    );
                    write!(state, r#"
        inline {ty}({as_std_function} f);"#, ty = self.ty.path.name())?;
                }
                Some(tr @ RustTrait::Normal { .. }) => {
                    let tr = tr.into_cpp();
                    write!(state, r#"
        inline {ref_kind}({tr}& arg);"#)?;
                }
                None => (),
            }
            if let Some((_, cpp_ty)) = &self.cpp_value {
                    if ref_kind == "Ref" {
                    write!(state, r#"
        inline {cpp_ty} const& cpp() const {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
        // inline {cpp_ty} const& cpp() const {{ return *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
                    write!(state, r#"
        inline {ref_kind}(const {cpp_ty}& t) : data(reinterpret_cast<size_t>(&t)) {{}}"#)?;
                } else {
                    write!(state, r#"
        inline {cpp_ty} const& cpp() const {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
        // inline {cpp_ty} const& cpp() const {{ return *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
                    write!(state, r#"
        inline {cpp_ty}& cpp() {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty}*>(data); }}"#)?;
        // inline {cpp_ty}& cpp() {{ return *reinterpret_cast<{cpp_ty}*>(data); }}"#)?;
                    write!(state, r#"
        inline {ref_kind}({cpp_ty}& t) : data(reinterpret_cast<size_t>(&t)) {{}}"#)?;
                }
            }
            if let Some(cpp_ty) = &self.cpp_ref {
                if ref_kind == "Ref" {
                    write!(state, r#"
        inline {cpp_ty} const& cpp() const {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
        // inline {cpp_ty} const& cpp() const {{ return *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
                    write!(state, r#"
        inline {ref_kind}(const {cpp_ty}& t) : data(reinterpret_cast<size_t>(&t)) {{}}"#)?;
                } else {
                    write!(state, r#"
        inline {cpp_ty} const& cpp() const {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject const*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
        // inline {cpp_ty} const& cpp() const {{ return *reinterpret_cast<{cpp_ty} const*>(data); }}"#)?;
                    write!(state, r#"
        inline {cpp_ty}& cpp() {{ return reinterpret_cast<ZngurCppOpaqueOwnedObject*>(data)->is_owned() ? reinterpret_cast<ZngurCppOpaqueOwnedObject*>(data)->as_cpp<{cpp_ty}>() : *reinterpret_cast<{cpp_ty}*>(data); }}"#)?;
        // inline {cpp_ty}& cpp() {{ return *reinterpret_cast<{cpp_ty}*>(data); }}"#)?;
                    write!(state, r#"
        inline {ref_kind}({cpp_ty}& t) : data(reinterpret_cast<size_t>(&t)) {{}}"#)?;
                }
            }
            for method in &self.methods {
                if let ZngurMethodReceiver::Ref(m, _) = method.kind {
                    if m == Mutability::Mut && ref_kind == "Ref" {
                        continue;
                    }
                    let CppFnSig {
                        rust_link_name: _,
                        inputs,
                        output,
                    } = &method.sig;
                    write!(state, "\n        {output} {fn_name}({input_defs}) const;",
                        fn_name = &method.name,
                        input_defs = inputs
                            .iter()
                            .skip(1)
                            .enumerate()
                            .map(|(n, ty)| format!("{ty} i{n}"))
                            .join(", "),
                    )?;
                }
            }
            if self.ty.path.to_string() == "::rust::Str" && ref_kind == "Ref" {
                write!(state, r#"
        friend Str;
    }};
    inline Ref<::rust::Str> Str::from_char_star(const char* s) {{
        Ref<Str> o;
        o.data[0] = reinterpret_cast<size_t>(s);
        o.data[1] = strlen(s);
        return o;
    }}"#)?;
            } else {
                write!(state, "\n    }};")?;
            }
            write!(state, r#"
    template<> inline uint8_t* __zngur_internal_data_ptr<{ref_kind}<{ty}>>(const {ref_kind}<{ty}>& t) {{ return const_cast<uint8_t*>(reinterpret_cast<const uint8_t*>(&t.data)); }}
    template<> inline void __zngur_internal_assume_init<{ref_kind}<{ty}>>({ref_kind}<{ty}>&) {{ }}
    template<> inline void __zngur_internal_check_init<{ref_kind}<{ty}>>(const {ref_kind}<{ty}>&) {{ }}
    template<> inline void __zngur_internal_assume_deinit<{ref_kind}<{ty}>>({ref_kind}<{ty}>&) {{ }}
    template<> inline size_t __zngur_internal_size_of<{ref_kind}<{ty}>>() {{ return {size}; }}
}}"#,
                ty = self.ty,
                size = if is_unsized { 16 } else { 8 },
            )?;
        }
        if let Some(cpp_ty) = self.cpp_ref.as_ref().map(|s| s.as_str())
            .or_else(|| if self.alias.is_none() { self.cpp_value.as_ref().map(|(_, v)| v.as_str()) } else { None })
        {
            // let cpp_ty = parse_cpp_inner_val_ty(cpp_ty);
            if let Some(alias) = &self.alias {
                write!(state, "\ntemplate<> struct __zngur__to_rust<{cpp_ty}> {{ typedef ::rust::{ty} type; }};", ty = alias)?;
                write!(state, "\ntemplate<> struct __zngur__from_rust<::rust::{ty}> {{ typedef {cpp_ty} type; }};", ty = alias)?;
            } else {
                write!(state, "\ntemplate<> struct __zngur__to_rust<{cpp_ty}> {{ typedef {ty} type; }};", ty = self.ty)?;
                write!(state, "\ntemplate<> struct __zngur__from_rust<{ty}> {{ typedef {cpp_ty} type; }};", ty = self.ty)?;
            }
        }
        Ok(())
    }

    fn emit(&self, state: &mut State) -> std::fmt::Result {
        let is_copy = self
            .wellknown_traits
            .contains(&ZngurWellknownTraitData::Copy);
        write!(state, r#"
namespace rust {{
    template<> inline uint8_t* __zngur_internal_data_ptr<{ty}>(const {ty}& t);
    template<> inline void __zngur_internal_check_init<{ty}>(const {ty}& t);
    template<> inline void __zngur_internal_assume_init<{ty}>({ty}& t);
    template<> inline void __zngur_internal_assume_deinit<{ty}>({ty}& t);
    template<> inline size_t __zngur_internal_size_of<{ty}>();
}}"#,
            ty = self.ty,
        )?;
        self.ty.path.emit_in_namespace(state, |state| {
            if self.ty.path.is_unit() {
                write!(state, "\n{}template<> struct Tuple<> {{ ::std::array<::uint8_t, 1> data; }};", state.indent())?;
                return Ok(());
            } else {
                self.ty.emit_specialization_decl(state)?;
            }
            match self.layout {
                CppLayoutPolicy::OnlyByRef => {
                    write!(state, r#" {{
    public:
        {ty}() = delete;"#,
                        ty = self.ty.path.name())?;
                    if self.ty.path.to_string() == "::rust::Str" {
                        write!(state, r#"
        static inline ::rust::Ref<::rust::Str> from_char_star(const char* s);"#)?;
                    }
                }
                CppLayoutPolicy::HeapAllocated { .. } | CppLayoutPolicy::StackAllocated { .. } => {
                    match self.layout {
                        CppLayoutPolicy::StackAllocated { size, align } => {
                            let size = size.max(1);
                            write!(state, r#" {{
    private:
        alignas({align}) mutable ::std::array<uint8_t, {size}> data;"#,
                            )?;
                        }
                        CppLayoutPolicy::HeapAllocated { .. } => {
                            write!(state, r#" {{
    private:
        uint8_t* data;"#)?;
                        }
                        CppLayoutPolicy::OnlyByRef => unreachable!(),
                    }
                    write!(state, r#"
        friend uint8_t* ::rust::__zngur_internal_data_ptr<{ty}>(const {ty}& t);
        friend void ::rust::__zngur_internal_check_init<{ty}>(const {ty}& t);
        friend void ::rust::__zngur_internal_assume_init<{ty}>({ty}& t);
        friend void ::rust::__zngur_internal_assume_deinit<{ty}>({ty}& t);
        friend void ::rust::zngur_pretty_print<{ty}>({ty} const& t);"#,
                        ty = self.ty,
                    )?;
                    if self.ty.path.to_string() == "::rust::Bool" {
                        assert_eq!(
                            self.layout,
                            CppLayoutPolicy::StackAllocated { size: 1, align: 1 }
                        );
                        assert!(is_copy);
                        write!(state, r#"
    public:
        operator bool() const {{ return data[0] != 0; }}
        Bool(bool b) {{ data[0] = b; }}
    private:"#,
                        )?;
                    }
                    if !is_copy {
                        write!(state, "\n        bool drop_flag;")?;
                    }
                    let (alloc_heap, free_heap, copy_data) = match &self.layout {
                        CppLayoutPolicy::StackAllocated { .. } => (
                            "".to_owned(),
                            "".to_owned(),
                            "this->data = other.data;".to_owned(),
                        ),
                        CppLayoutPolicy::HeapAllocated {
                            size_fn,
                            alloc_fn,
                            free_fn,
                        } => (
                            format!("data = {alloc_fn}();"),
                            format!("{free_fn}(data);"),
                            format!("memcpy(this->data, other.data, {size_fn}());"),
                        ),
                        CppLayoutPolicy::OnlyByRef => unreachable!(),
                    };
                    write!(state, "\n    public:")?;
                    if is_copy {
                        write!(state, r#"
        {ty}() {{ {alloc_heap} }}
        ~{ty}() {{ {free_heap} }}
        {ty}(const {ty}& other) {{
            {alloc_heap}
            {copy_data}
        }}
        {ty}& operator=(const {ty}& other) {{
            {copy_data}
            return *this;
        }}
        {ty}({ty}&& other) {{
            {alloc_heap}
            {copy_data}
        }}
        {ty}& operator=({ty}&& other) {{
            {copy_data}
            return *this;
        }}"#,
                            ty = self.ty.path.name(),
                        )?;
                    } else {
                        let api = if state.hotreload { "GetZngurRsApi()." } else { "" };
                        let drop_in_place = self
                            .wellknown_traits
                            .iter()
                            .find_map(|x| match x {
                                ZngurWellknownTraitData::Drop { drop_in_place } => {
                                    Some(drop_in_place)
                                }
                                _ => None,
                            })
                            .unwrap();
                        write!(state, r#"
        {ty}() : drop_flag(false) {{ {alloc_heap} }}
        ~{ty}() {{
            if (drop_flag) {{ {api}{drop_in_place}(&data[0]); }}{free_heap}
        }}
        {ty}(const {ty}& other) = delete;
        {ty}& operator=(const {ty}& other) = delete;
        {ty}({ty}&& other) : drop_flag(false) {{
            {alloc_heap}*this = ::std::move(other);
        }}
        {ty}& operator=({ty}&& other) {{
            if (this != &other) {{
                if (drop_flag) {{ {api}{drop_in_place}(&data[0]); }}
                this->drop_flag = other.drop_flag;
                {copy_data}
                other.drop_flag = false;
            }}
            return *this;
        }}"#,
                            ty = self.ty.path.name(),
                        )?;
                    }
                    match &self.from_trait {
                        Some(RustTrait::Fn { inputs, output, .. }) => {
                            let as_std_function = format!(
                                "::std::function<{}({})>",
                                output.into_cpp(),
                                inputs.iter().map(|x| x.into_cpp()).join(", ")
                            );
                            write!(state, r#"
        static inline {ty} make_box({as_std_function} f);"#,
                                ty = self.ty.path.name(),
                            )?;
                        }
                        Some(RustTrait::Normal { .. }) => {
                            write!(state, r#"
                        template<typename T, typename... Args> static {ty} make_box(Args&&... args);"#,
                                ty = self.ty.path.name(),
                            )?;
                        }
                        None => (),
                    }
                }
            }
            if let Some((rust_link_name, cpp_ty)) = &self.cpp_value {
                let api = if state.hotreload { "GetZngurRsApi()." } else { "" };
                write!(state, r#"
        inline {cpp_ty}& cpp() {{ return (*{api}{rust_link_name}(&data[0])).as_cpp<{cpp_ty}>(); }}"#)?;
                write!(state, r#"
        inline {cpp_ty} const& cpp() const {{ return (*{api}{rust_link_name}(&data[0])).as_cpp<{cpp_ty}>(); }}"#)?;
            }
            for method in &self.methods {
                write!(state, "\n        static ")?;
                method.sig.emit_cpp_header(state, &method.name)?;
                if method.kind != ZngurMethodReceiver::Static {
                    let CppFnSig {
                        rust_link_name: _,
                        inputs,
                        output,
                    } = &method.sig;
                    write!(state, "\n        {output} {fn_name}({input_defs}) {const_kw};",
                        fn_name = &method.name,
                        input_defs = inputs
                            .iter()
                            .skip(1)
                            .enumerate()
                            .map(|(n, ty)| format!("{ty} i{n}"))
                            .join(", "),
                        const_kw = if !matches!(method.kind, ZngurMethodReceiver::Ref(Mutability::Not, _)) {
                            ""
                        } else {
                            "const"
                        },
                    )?;
                }
            }
            for constructor in &self.constructors {
                write!(state, "\n        {fn_name}({input_defs});",
                    fn_name = &self.ty.path.0.last().unwrap(),
                    input_defs = constructor
                        .inputs
                        .iter()
                        .enumerate()
                        .map(|(n, ty)| format!("{ty} i{n}"))
                        .join(", "),
                )?;
            }
            write!(state, "\n    }};")
        })?;

        let ty = &self.ty;
        if self.layout != CppLayoutPolicy::OnlyByRef {
            match &self.layout {
                CppLayoutPolicy::StackAllocated { size, align: _ } => {
                    write!(state, r#"
namespace rust {{
    template<> inline size_t __zngur_internal_size_of<{ty}>() {{ return {size}; }}"#,
                    )?;
                }
                CppLayoutPolicy::HeapAllocated { size_fn, .. } => {
                    write!(state, r#"
namespace rust {{
    template<> inline size_t __zngur_internal_size_of<{ty}>() {{ return {size_fn}(); }}"#,
                    )?;
                }
                CppLayoutPolicy::OnlyByRef => unreachable!(),
            }

            if is_copy {
                write!(state, r#"
    template<> inline void __zngur_internal_check_init<{ty}>(const {ty}&) {{ }}
    template<> inline void __zngur_internal_assume_init<{ty}>({ty}&) {{ }}
    template<> inline void __zngur_internal_assume_deinit<{ty}>({ty}&) {{ }}"#,
                )?;
            } else {
                write!(state, r#"
    template<> inline void __zngur_internal_check_init<{ty}>(const {ty}& t) {{
        if (!t.drop_flag) {{
            ::std::cerr << "Use of uninitialized or moved Zngur Rust object with type {ty}" << ::std::endl;
            while (true) raise(SIGSEGV);
        }}
    }}
    template<> inline void __zngur_internal_assume_init<{ty}>({ty}& t) {{ t.drop_flag = true; }}
    template<> inline void __zngur_internal_assume_deinit<{ty}>({ty}& t) {{
        ::rust::__zngur_internal_check_init<{ty}>(t);
        t.drop_flag = false;
    }}"#,
                )?;
            }
            write!(state, r#"
    template<> inline uint8_t* __zngur_internal_data_ptr<{ty}>({ty} const & t) {{ return const_cast<uint8_t*>(&t.data[0]); }}
}}"#,
            )?;
        }
        self.emit_ref_specialization(state)?;

        if self.ty.is_enum {
            let to_struct_name = "ToRust";
            let to_method_name = "to";
            write!(state, r#"
template<> struct {to_struct_name}<{ty}::Type> {{
    typedef {path} type;
    static inline {path} {to_method_name}({ty}::Type t) {{"#, ty = self.ty.path.name(), path = self.ty.path)?;

            for (n, name) in self.alternates.iter().enumerate() {
                if self.alternates.len() > 1 {
                    if n == 0 {
                        write!(state, "\n        if ")?;
                    } else if n == self.alternates.len() - 1 {
                        write!(state, "\n        else ")?;
                    } else {
                        write!(state, "\n        else if ")?;
                    }
                }
                if n < self.alternates.len() - 1 {
                    write!(state, "(t == {ty}::{name}) return {path}::{name}();", ty = self.ty.path.name(), path = self.ty.path)?;
                } else {
                    write!(state, "return {path}::{name}();", path = self.ty.path)?;
                }
            }

            let from_struct_name = "FromRust";
            let from_method_name = "from";

            write!(state, r#"
    }}
}};
template<> struct {from_struct_name}<::rust::Ref<{path}>> {{
    typedef {ty}::Type type;
    static inline {ty}::Type {from_method_name}(::rust::Ref<{path}> const& t) {{"#, ty = self.ty.path.name(), path = self.ty.path)?;

            for (n, name) in self.alternates.iter().enumerate() {
                if self.alternates.len() > 1 {
                    if n == 0 {
                        write!(state, "\n        if ")?;
                    } else if n == self.alternates.len() - 1 {
                        write!(state, "\n        else ")?;
                    } else {
                        write!(state, "\n        else if ")?;
                    }
                }
                if n < self.alternates.len() - 1 {
                    write!(state, "(t.matches_{name}()) return {ty}::{name};", ty = self.ty.path.name())?;
                } else {
                    write!(state, "return {ty}::{name};", ty = self.ty.path.name())?;
                }
            }

            write!(state, r#"
    }}
}};
template<> struct {from_struct_name}<{path}> : public {from_struct_name}<rust::Ref<{path}>> {{
    static inline {ty}::Type {from_method_name}({path} const& t) {{ return {from_struct_name}<rust::Ref<{path}>>::{from_method_name}(t); }}
}};
"#, ty = self.ty.path.name(), path = self.ty.path)?;
        }

        std::fmt::Result::Ok(())
    }

    fn emit_cpp_fn_defs(
        &self,
        state: &mut State,
        traits: &HashMap<RustTrait, CppTraitDefinition>,
    ) -> std::fmt::Result {
        let is_unsized = self
            .wellknown_traits
            .contains(&ZngurWellknownTraitData::Unsized);
        let cpp_type = &self.ty.to_string();
        let my_name = cpp_type.strip_prefix("::").unwrap();
        let api = if state.hotreload { "GetZngurRsApi()." } else { "" };
        for c in &self.constructors {
            let is_owned_obj = c.inputs.iter().next().map(|ty| &ty.path.0 == &["rust", "ZngurCppOpaqueOwnedObject"]).unwrap_or_default();
            let fn_name = my_name.to_owned() + "::" + self.ty.path.0.last().unwrap();
            let CppFnSig {
                inputs,
                output: _,
                rust_link_name,
            } = c;
            write!(state, "\ninline {fn_name}({input_defs}) {{
    ::rust::__zngur_internal_assume_init(*this);
    {api}{rust_link_name}({input_args}::rust::__zngur_internal_data_ptr(*this));
    {owned}
    {deinits}
}}",
                input_defs = inputs
                    .iter()
                    .enumerate()
                    .map(|(n, ty)| format!("{ty} i{n}"))
                    .join(", "),
                input_args = (0..inputs.len())
                    .map(|n| format!("::rust::__zngur_internal_data_ptr(i{n}), "))
                    .join(""),
                owned = if !is_owned_obj { "" } else {
                    "reinterpret_cast<::rust::ZngurCppOpaqueOwnedObject&>(this->data).mark_owned();"
                },
                deinits = (0..inputs.len())
                    .map(|n| format!("::rust::__zngur_internal_assume_deinit(i{n});"))
                    .join("\n"),
            )?;
        }
        match self.from_trait.as_ref().and_then(|k| traits.get(k)) {
            Some(CppTraitDefinition::Fn { sig }) => {
                let as_std_function = format!(
                    "::std::function<{}({})>",
                    sig.output,
                    sig.inputs.iter().join(", ")
                );
                let ii_names = sig
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(n, x)| format!("::rust::__zngur_internal_move_from_rust<{x}>(i{n})"))
                    .join(", ");
                let uint8_t_ix = sig
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(n, _)| format!("uint8_t* i{n},"))
                    .join(" ");
                let out_ty = &sig.output;
                writeln!(
                    state,
                    r#"
{my_name} {my_name}::make_box({as_std_function} f) {{
    auto data = new {as_std_function}(f);
    {my_name} o;
    ::rust::__zngur_internal_assume_init(o);
    {api}{link_name}(
        reinterpret_cast<uint8_t*>(data),
        [](uint8_t *d) {{ delete reinterpret_cast<{as_std_function}*>(d); }},
        [](uint8_t *d, {uint8_t_ix} uint8_t *o) {{
            auto dd = reinterpret_cast<{as_std_function} *>(d);
            {out_ty} oo = (*dd)({ii_names});
            ::rust::__zngur_internal_move_to_rust<{out_ty}>(o, oo);
        }},
        ::rust::__zngur_internal_data_ptr(o)
    );
    return o;
}}"#,
                    link_name = sig.rust_link_name,
                )?;
            }
            Some(CppTraitDefinition::Normal {
                as_ty,
                methods: _,
                link_name,
                link_name_ref: _,
            }) => {
                write!(state, r#"
template<typename T, typename... Args> {my_name} {my_name}::make_box(Args&&... args) {{
    auto data = new T(::std::forward<Args>(args)...);
    auto data_as_impl = dynamic_cast<{as_ty}*>(data);
    {my_name} o;
    ::rust::__zngur_internal_assume_init(o);
    {api}{link_name}(
        reinterpret_cast<uint8_t*>(data_as_impl),
        [](uint8_t *d) {{ delete reinterpret_cast<{as_ty} *>(d); }},"#)?;
                writeln!(state, r#"
        ::rust::__zngur_internal_data_ptr(o)
    );
    return o;
}}"#,
                )?;
            }
            None => (),
        }
        match self.from_trait_ref.as_ref().and_then(|k| traits.get(k)) {
            Some(CppTraitDefinition::Fn { .. }) => {
                todo!()
            }
            Some(CppTraitDefinition::Normal {
                as_ty,
                methods: _,
                link_name: _,
                link_name_ref,
            }) => {
                for ref_kind in ["Ref", " RefMut"] {
                    writeln!(
                        state,
                        r#"
rust::{ref_kind}<{my_name}>::{ref_kind}({as_ty}& args) {{
    auto data_as_impl = &args;
    ::rust::__zngur_internal_assume_init(*this);
    {link_name_ref}(
        (uint8_t *)data_as_impl,"#,
                    )?;
                    writeln!(
                        state,
                        r#"
        ::rust::__zngur_internal_data_ptr(*this)
    );
}}"#,
                    )?;
                }
            }
            None => (),
        }
        for method in &self.methods {
            let fn_name = my_name.to_owned() + "::" + &method.name;
            method.sig.emit_cpp_def(state, &fn_name)?;
            if let ZngurMethodReceiver::Ref(m, _) = method.kind {
                let ref_kinds: &[&str] = match m {
                    Mutability::Mut => &["RefMut"],
                    Mutability::Not => &["Ref", "RefMut"],
                };
                for ref_kind in ref_kinds {
                    let CppFnSig {
                        rust_link_name: _,
                        inputs,
                        output,
                    } = &method.sig;
                    write!(state, "\ninline {output} rust::{ref_kind}<{ty}>::{method_name}({input_defs}) const {{ return {fn_name}(*this{input_args}); }}",
                        ty = &self.ty,
                        method_name = &method.name,
                        input_defs = inputs
                            .iter()
                            .skip(1)
                            .enumerate()
                            .map(|(n, ty)| format!("{ty} i{n}"))
                            .join(", "),
                        input_args = (0..inputs.len() - 1)
                            .map(|n| format!(", ::std::move(i{n})"))
                            .join("")
                    )?;
                }
            }
            if !is_unsized && method.kind != ZngurMethodReceiver::Static {
                let CppFnSig {
                    rust_link_name: _,
                    inputs,
                    output,
                } = &method.sig;
                write!(state, "\ninline {output} {fn_name}({input_defs}) {const_kw} {{ return {fn_name}({this_arg}{input_args}); }}",
                    this_arg = match method.kind {
                        ZngurMethodReceiver::Ref(_, _) => "*this",
                        ZngurMethodReceiver::Move => "::std::move(*this)",
                        ZngurMethodReceiver::Static => unreachable!(),
                    },
                    input_defs = inputs
                        .iter()
                        .skip(1)
                        .enumerate()
                        .map(|(n, ty)| format!("{ty} i{n}"))
                        .join(", "),
                    input_args = (0..inputs.len() - 1)
                        .map(|n| format!(", ::std::move(i{n})"))
                        .join(""),
                    const_kw = if !matches!(method.kind, ZngurMethodReceiver::Ref(Mutability::Not, _)) {
                        ""
                    } else {
                        "const"
                    },
                )?;
            }
        }
        let api = if state.hotreload { "GetZngurRsApi()." } else { "" };
        for tr in &self.wellknown_traits {
            match tr {
                ZngurWellknownTraitData::Debug {
                    pretty_print,
                    debug_print: _, // TODO: use it
                } => {
                    write!(state, r#"
namespace rust {{
    template<> inline void zngur_pretty_print<{ty}>({ty} const& t) {{
        ::rust::__zngur_internal_check_init<{ty}>(t);
        {api}{pretty_print}(&t.data[0]);
    }}
}}"#,
                        ty = self.ty,
                    )?;
                }
                ZngurWellknownTraitData::Unsized
                | ZngurWellknownTraitData::Copy
                | ZngurWellknownTraitData::Drop { .. } => {}
            }
        }
        Ok(())
    }

    pub fn emit_links(&self, state: &mut EmitMode<impl Write>) -> std::fmt::Result {
        for method in &self.methods {
            method.sig.emit_link_decl(state)?;
        }
        for c in &self.constructors {
            c.emit_link_decl(state)?;
        }
        if let Some(cpp_value) = &self.cpp_value {
            match state {
                EmitMode::Cpp(state, hotreload) => {
                    if *hotreload {
                        writeln!(state, "    ::rust::ZngurCppOpaqueOwnedObject* (*{})(uint8_t*);", cpp_value.0)?;
                    } else {
                        writeln!(state, "::rust::ZngurCppOpaqueOwnedObject* {}(uint8_t*);", cpp_value.0)?;
                    }
                }
                EmitMode::Rust(state) => {
                    write!(state, "\n    pub {}: extern \"C\" fn(v: *mut u8) -> *mut ZngurCppOpaqueOwnedObject,", cpp_value.0)?;
                }
                EmitMode::RustLinkNameOnly(state) => {
                    write!(state, "\n        {},", cpp_value.0)?;
                }
            }
        }
        if let CppLayoutPolicy::HeapAllocated {
            size_fn,
            alloc_fn,
            free_fn,
        } = &self.layout
        {
            writeln!(state, "size_t {size_fn}();")?;
            writeln!(state, "uint8_t* {alloc_fn}();")?;
            writeln!(state, "void {free_fn}(uint8_t*);")?;
        }
        for tr in &self.wellknown_traits {
            match tr {
                ZngurWellknownTraitData::Debug {
                    pretty_print,
                    debug_print,
                } => {
                    match state {
                        EmitMode::Cpp(state, hotreload) => {
                            if *hotreload {
                                writeln!(state, "    void (*{pretty_print})(uint8_t *data);")?;
                                writeln!(state, "    void (*{debug_print})(uint8_t *data);")?;
                            } else {
                                writeln!(state, "void {pretty_print}(uint8_t *data);")?;
                                writeln!(state, "void {debug_print}(uint8_t *data);")?;
                            }
                        }
                        EmitMode::Rust(state) => {
                            write!(state, "\n    pub {pretty_print}: extern \"C\" fn(data: *mut u8),")?;
                            write!(state, "\n    pub {debug_print}: extern \"C\" fn(data: *mut u8),")?;
                        }
                        EmitMode::RustLinkNameOnly(state) => {
                            write!(state, "\n        {pretty_print},")?;
                            write!(state, "\n        {debug_print},")?;
                        }
                    }
                }
                ZngurWellknownTraitData::Unsized | ZngurWellknownTraitData::Copy => (),
                ZngurWellknownTraitData::Drop { drop_in_place } => {
                    match state {
                        EmitMode::Cpp(state, hotreload) => {
                            if *hotreload {
                                writeln!(state, "    void (*{drop_in_place})(uint8_t *data);")?;
                            } else {
                                writeln!(state, "void {drop_in_place}(uint8_t *data);")?;
                            }
                        }
                        EmitMode::Rust(state) => {
                            write!(state, "\n    pub {drop_in_place}: extern \"C\" fn(data: *mut u8),")?;
                        }
                        EmitMode::RustLinkNameOnly(state) => {
                            write!(state, "\n        {drop_in_place},")?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Default)]
pub struct CppFile {
    pub type_defs: Vec<CppTypeDefinition>,
    pub trait_defs: HashMap<RustTrait, CppTraitDefinition>,
    pub fn_defs: Vec<CppFnDefinition>,
    pub exported_fn_defs: Vec<CppExportedFnDefinition>,
    pub exported_impls: Vec<CppExportedImplDefinition>,
    pub additional_includes: String,
    pub panic_to_exception: bool,
}

impl CppFile {
    fn emit_h_file(&self, state: &mut State) -> std::fmt::Result {
        state.text += r#"#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <csignal>
#include <array>
#include <iostream>
#include <functional>
#include <math.h>"#;
        state.text += &self.additional_includes;
        if self.panic_to_exception {
            state.text += r#"
            namespace rust { class Panic {}; }
            extern "C" {
                uint8_t __zngur_detect_panic();
                void __zngur_take_panic();
            }
            "#;
        }
        state.text += r#"
#define zngur_dbg(x) (::rust::zngur_dbg_impl(__FILE__, __LINE__, #x, x))"#;

        state.text += if state.hotreload {
            r#"
#define INITIALIZE_ZNGUR_API(api_ptr) __zngur_init_api(api_ptr);
#define ZNGUR_API_OK() __ZNGUR_RSAPI_INITIALIZED
#define DECLARE_ZNGUR_API() \
    static bool __ZNGUR_RSAPI_INITIALIZED = false; \
    static ZngurRsApi __ZNGUR_RSAPI; \
    ZngurRsApi& GetZngurRsApi() { assert(ZNGUR_API_OK()); return __ZNGUR_RSAPI; } \
    ZngurCApi __zngur_get_capi(); \
    template<typename T> inline void __zngur_init_api(T api_ptr) { \
        auto get_rsapi_fn = (ZngurGetRsApiFn)api_ptr; \
        if (get_rsapi_fn != nullptr) { \
            __ZNGUR_RSAPI = (*get_rsapi_fn)(__zngur_get_capi()); \
            __ZNGUR_RSAPI_INITIALIZED = true; \
        } \
    }"#
        } else {
            ""
        };
        state.text += r#"
template<typename T> struct _MISSING_TO_RUST_CONVERSION_TYPE_;
template<typename T> struct _MISSING_FROM_RUST_CONVERSION_TYPE_;
template<typename T> struct ToRust { static_assert(sizeof(_MISSING_TO_RUST_CONVERSION_TYPE_<T>) == -1, "ToRust"); };
template<typename T> struct FromRust { static_assert(sizeof(_MISSING_FROM_RUST_CONVERSION_TYPE_<T>) == -1, "FromRust"); };
"#;
        state.text += r#"
#define PTR_TAG_MASK 0x1UL
#define PTR_TAG_SET(p, flag) (reinterpret_cast<decltype(p)>((reinterpret_cast<uintptr_t>(p) & ~PTR_TAG_MASK) | ((flag) ? PTR_TAG_MASK : 0)))
#define PTR_TAG_GET(p) ((reinterpret_cast<uintptr_t>(p) & PTR_TAG_MASK) != 0)
#define PTR_TAG_CLEAR(p) (reinterpret_cast<decltype(p)>(reinterpret_cast<uintptr_t>(p) & ~PTR_TAG_MASK))

template<typename T> struct __zngur__to_rust { static_assert(sizeof(_MISSING_TO_RUST_CONVERSION_TYPE_<T>) == -1, "to_rust"); };
template<typename T> struct __zngur__from_rust { static_assert(sizeof(_MISSING_FROM_RUST_CONVERSION_TYPE_<T>) == -1, "from_rust"); };

namespace rust {
    template<typename T> uint8_t* __zngur_internal_data_ptr(const T& t);
    template<typename T> void __zngur_internal_assume_init(T& t);
    template<typename T> void __zngur_internal_assume_deinit(T& t);
    template<typename T> inline size_t __zngur_internal_size_of();
    template<typename T> inline void __zngur_internal_move_to_rust(uint8_t* dst, T& t) {
        memcpy(dst, ::rust::__zngur_internal_data_ptr(t), ::rust::__zngur_internal_size_of<T>());
        ::rust::__zngur_internal_assume_deinit(t);
    }
    template<typename T> inline T __zngur_internal_move_from_rust(uint8_t* src) {
        T t;
        ::rust::__zngur_internal_assume_init(t);
        memcpy(::rust::__zngur_internal_data_ptr(t), src, ::rust::__zngur_internal_size_of<T>());
        return t;
    }
    template<typename T> inline void __zngur_internal_check_init(const T& t) { }
    class ZngurCppOpaqueOwnedObject {
        uint8_t* data;
        void (*destructor)(uint8_t*);
    public:
        template<typename T, typename... Args> inline static ZngurCppOpaqueOwnedObject build(Args&&... args) {
            ZngurCppOpaqueOwnedObject o;
            o.data = reinterpret_cast<uint8_t*>(new T(::std::forward<Args>(args)...));
            o.destructor = [](uint8_t* d) { delete reinterpret_cast<T*>(PTR_TAG_CLEAR(d)); };
            return o;
        }
        void mark_owned() { data = PTR_TAG_SET(data, true); }
        bool is_owned() const { return PTR_TAG_GET(data); }
        template<typename T> inline T& as_cpp() { return *reinterpret_cast<T*>(PTR_TAG_CLEAR(data)); }
        template<typename T> inline T const& as_cpp() const { return *reinterpret_cast<T const*>(PTR_TAG_CLEAR(data)); }
    };
"#;
        state.text += r#"
    template<typename T> struct Ref;
    template<typename T> struct RefMut;
    template<typename... T> struct Tuple;
    using Unit = Tuple<>;
    template<typename T> void zngur_pretty_print(const T&);
    class Inherent;
    template<typename Type, typename Trait = Inherent> class Impl;
    template<typename T> T&& zngur_dbg_impl(const char* file_name, int line_number, const char* exp, T&& input) {
        ::std::cerr << "[" << file_name << ":" << line_number << "] " << exp << " = ";
        zngur_pretty_print<typename ::std::remove_reference<T>::type>(input);
        return ::std::forward<T>(input);
    }
    template<> inline size_t __zngur_internal_size_of<unsigned char*>() { return sizeof(unsigned char*); }
    template<> inline size_t __zngur_internal_size_of<const unsigned char*>() { return sizeof(const unsigned char*); }
    "#;
        for (ty, ok_for_android) in [8, 16, 32, 64]
            .into_iter()
            .flat_map(|x| [(format!("int{x}_t"), true), (format!("uint{x}_t"), true)])
            .chain([8, 16, 32, 64].into_iter().flat_map(|x| {
                [
                    (format!("::rust::Ref<int{x}_t>"), true),
                    (format!("::rust::Ref<uint{x}_t>"), true),
                    (format!("::rust::RefMut<int{x}_t>"), true),
                    (format!("::rust::RefMut<uint{x}_t>"), true),
                ]
            }))
            .chain([
                ("::rust::ZngurCppOpaqueOwnedObject".to_string(), true),
                ("::double_t".to_string(), true),
                ("::float_t".to_string(), true),
                ("unsigned long".to_string(), false),
            ])
        {
          if !ok_for_android { write!(state, "\n#if !PLATFORM_ANDROID\n")?; }
            write!(state, r#"
    template<> inline uint8_t* __zngur_internal_data_ptr<{ty}>(const {ty}& t) {{ return const_cast<uint8_t*>(reinterpret_cast<const uint8_t*>(&t)); }}
    template<> inline void __zngur_internal_assume_init<{ty}>({ty}&) {{}}
    template<> inline void __zngur_internal_assume_deinit<{ty}>({ty}&) {{}}
    template<> inline size_t __zngur_internal_size_of<{ty}>() {{ return sizeof({ty}); }}
    template<> inline uint8_t* __zngur_internal_data_ptr<{ty}*>({ty}* const & t) {{ return const_cast<uint8_t*>(reinterpret_cast<const uint8_t*>(&t)); }}
    template<> inline void __zngur_internal_assume_init<{ty}*>({ty}*&) {{}}
    template<> inline void __zngur_internal_assume_deinit<{ty}*>({ty}*&) {{}}
    template<> inline uint8_t* __zngur_internal_data_ptr<{ty} const*>({ty} const* const & t) {{ return const_cast<uint8_t*>(reinterpret_cast<const uint8_t*>(&t)); }}
    template<> inline void __zngur_internal_assume_init<{ty} const*>({ty} const*&) {{}}
    template<> inline void __zngur_internal_assume_deinit<{ty} const*>({ty} const*&) {{}}
    template<> struct Ref<{ty}> {{
        Ref() {{ data = 0; }}
        Ref(const {ty}& t) {{ data = reinterpret_cast<size_t>(__zngur_internal_data_ptr(t)); }}
        {ty}& operator*() {{ return *reinterpret_cast<{ty}*>(data); }}
    private:
        size_t data;
        friend uint8_t* ::rust::__zngur_internal_data_ptr<Ref<{ty}>>(const ::rust::Ref<{ty}>& t);
    }};
    template<> struct RefMut<{ty}> {{
        RefMut() {{ data = 0; }}
        RefMut({ty}& t) {{ data = reinterpret_cast<size_t>(__zngur_internal_data_ptr(t)); }}
        {ty}& operator*() {{ return *reinterpret_cast<{ty}*>(data); }}
    private:
        size_t data;
        friend uint8_t* ::rust::__zngur_internal_data_ptr<RefMut<{ty}>>(const ::rust::RefMut<{ty}>& t);
    }};"#)?;
            if !ok_for_android { write!(state, "\n#endif // !PLATFORM_ANDROID\n")?; }
        }
        writeln!(state, "}}")?;

        // TODO: this section needs deduping, but c++ doesn't seem to mind
        self.emit_links(&mut EmitMode::Cpp(state, state.hotreload))?;
        for td in &self.type_defs {
            td.ty.emit_header(state)?;
        }
        for imp in &self.exported_impls {
            imp.ty.emit_header(state)?;
            if let Some(tr) = &imp.tr {
                tr.emit_header(state)?;
            }
        }
        for (_, td) in &self.trait_defs {
            if let CppTraitDefinition::Normal { as_ty, .. } = td {
                as_ty.emit_header(state)?;
            }
        }

        for (_, td) in &self.trait_defs {
            td.emit(state)?;
        }
        for td in &self.type_defs {
            td.emit(state)?;
        }
        for td in &self.type_defs {
            td.emit_cpp_fn_defs(state, &self.trait_defs)?;
        }
        for fd in &self.fn_defs {
            fd.emit_cpp_def(state)?;
        }
        for func in &self.exported_fn_defs {
            write!(state, "\nnamespace rust {{ namespace exported_functions {{")?;
            write!(state, "\n   {} {}(",
                if func.sig.output.is_void() { "void".to_string() } else { format!("{}", func.sig.output) },
                func.name
            )?;
            for (n, ty) in func.sig.inputs.iter().enumerate() {
                if n != 0 {
                    write!(state, ", ")?;
                }
                write!(state, "{ty} i{n}")?;
            }
            write!(state, ");")?;
            write!(state, "\n}} }}")?;
        }
        for imp in &self.exported_impls {
            write!(state, r#"
namespace rust {{
    template<> class Impl<{}, {}> {{
    public:"#,
                imp.ty,
                match &imp.tr {
                    Some(x) => format!("{x}"),
                    None => "::rust::Inherent".to_string(),
                }
            )?;
            for (name, sig) in &imp.methods {
                write!(state, "\n       static {} {}(",
                    if sig.output.is_void() { "void".to_string() } else { format!("{}", sig.output) },
                    name
                )?;
                for (n, ty) in sig.inputs.iter().enumerate() {
                    if n != 0 {
                        write!(state, ", ")?;
                    }
                    write!(state, "{ty} i{n}")?;
                }
                write!(state, ");")?;
            }
            write!(state, "\n    }};\n}}")?;
        }

        write!(state, r#"
namespace zngur {{
    template<typename T> using to_rust_t = typename ::__zngur__to_rust<T>::type;
    template<typename T> using from_rust_t = typename ::__zngur__from_rust<T>::type;
}}

// TO
template<typename T> struct ToRust<T&> {{ static_assert(sizeof(_MISSING_TO_RUST_CONVERSION_TYPE_<T>) == -1, "ToRust (ref or cref needed)");  }};
template<typename T> struct ToRust<T const&> {{ typedef ::rust::Ref<::zngur::to_rust_t<T>> type; static inline type to(T const& t) {{ return type(t); }} }};
template<typename T> struct ToRust<T&&> : public ToRust<T> {{}}; // pass by value
template<typename T> struct ToRust<T const&&> : public ToRust<T> {{}}; // pass by value
template<typename T> struct ToRust<std::reference_wrapper<T const>> : public ToRust<T const&> {{}};
template<typename T> struct ToRust<std::reference_wrapper<T const>&&> : public ToRust<T const&> {{}};
template<typename T> struct ToRust<std::reference_wrapper<T>> {{ typedef ::rust::RefMut<::zngur::to_rust_t<T>> type; static inline type to(T& t) {{ return type(t); }} }};
template<typename T> struct ToRust<std::reference_wrapper<T>&&> : public ToRust<std::reference_wrapper<T>> {{}};
// FROM
template<typename T> struct FromRust<T&> {{ static_assert(sizeof(_MISSING_FROM_RUST_CONVERSION_TYPE_<T>) == -1, "FromRust (ref or cref might be needed)");  }};
template<typename T> struct FromRust<T const&> {{ static_assert(sizeof(_MISSING_FROM_RUST_CONVERSION_TYPE_<T>) == -1, "FromRust (ref or cref might be needed)");  }};
template<typename T> struct FromRust<T&&> : public FromRust<T> {{}}; // pass by value
template<typename T> struct FromRust<T const&&> : public FromRust<T> {{}}; // pass by value
template<typename T> struct FromRust<::rust::RefMut<T>> {{ typedef ::zngur::from_rust_t<T>& type; static inline type from(::rust::RefMut<T>&& t) {{ return t.cpp(); }} }};
template<typename T> struct FromRust<::rust::Ref<T>> {{ typedef ::zngur::from_rust_t<T> const& type; static inline type from(::rust::Ref<T> const& t) {{ return t.cpp(); }} }};
template<typename T> struct FromRust<std::reference_wrapper<::rust::Ref<T> const>> : public FromRust<::rust::Ref<T>> {{}};
"#)?;

        for td in &self.type_defs {
            if let Some((_, cpp_ty)) = &td.cpp_value {
                write!(state, "\ntemplate<> struct ToRust<{cpp_ty}> {{ typedef ::zngur::to_rust_t<{cpp_ty}> type; static inline type to({cpp_ty} const& t) {{ return type(::rust::ZngurCppOpaqueOwnedObject::build<{cpp_ty}>(t)); }} }};")?;
                write!(state, "\ntemplate<> struct FromRust<{ty}> {{ typedef ::zngur::from_rust_t<{ty}> type; static inline type from({ty} const& t) {{ return t.cpp(); }} }};", ty = td.ty)?;
            }
        }

        write!(state, r#"
template<typename T> inline typename ToRust<T&&>::type _ToRs(T&& t) {{ return ToRust<T&&>::to(std::forward<T>(t)); }}
template<typename T> inline typename FromRust<T&&>::type _FromRs(T&& t) {{ return FromRust<T&&>::from(std::forward<T>(t)); }}

#ifndef ToRs_cref
#  define ToRs_cref(x) _ToRs(std::cref(x))
#endif
#ifndef ToRs_ref
#  define ToRs_ref(x) _ToRs(std::ref(x))
#endif
#ifndef ToRs_nomove
#  define ToRs_nomove(x) _ToRs(x)
#endif
#ifndef ToRs
#  define ToRs(x) _ToRs(std::move(x))
#endif

#ifndef FromRs_nomove
#  define FromRs_nomove(x) _FromRs(x)
#endif
#ifndef FromRs
#  define FromRs(x) _FromRs(std::move(x))
#endif
"#)?;

        Ok(())
    }

    fn emit_links(&self, state: &mut EmitMode<impl Write>) -> std::fmt::Result {
        if state.hotreload() {
            writeln!(state, "struct ZngurRsApi {{")?;
        } else {
            writeln!(state, "extern \"C\" {{")?;
        }
        for f in &self.fn_defs {
            f.sig.emit_link_decl(state)?;
        }
        for td in &self.type_defs {
            td.emit_links(state)?;
        }
        for (_, td) in &self.trait_defs {
            td.emit_links(state)?;
        }
        if state.hotreload() {
            write!(state, "}};")?;
            write!(state, "\nstruct ZngurCApi {{")?;
            for func in &self.exported_fn_defs {
                write!(state, "\n    void (*{})(", func.sig.rust_link_name)?;
                func.sig.emit_params(state)?;
                write!(state, ");")?;
            }
            for imp in &self.exported_impls {
                for (_, sig) in &imp.methods {
                    write!(state, "\n    void (*{})(", sig.rust_link_name)?;
                    sig.emit_params(state)?;
                    write!(state, ");")?;
                }
            }
            write!(state, "\n}};")?;
            write!(state, "\nZngurRsApi& GetZngurRsApi();")?;
            write!(state, "\nZngurCApi __zngur_get_capi();")?;
            write!(state, "\ntypedef ZngurRsApi(*ZngurGetRsApiFn)(ZngurCApi);")?;
        } else {
            write!(state, "\n}}")?;
        }
        Ok(())
    }

    fn emit_cpp_file(&self, state: &mut State, is_really_needed: &mut bool) -> std::fmt::Result {
        writeln!(state, r#"#include "./generated.h""#)?;
        writeln!(state, "extern \"C\" {{")?;
        for t in &self.trait_defs {
            *is_really_needed = true;
            t.1.emit_cpp(state)?;
        }
        for func in &self.exported_fn_defs {
            *is_really_needed = true;
            func.sig.emit_link(&mut EmitMode::Cpp(state, state.hotreload), false)?;
            writeln!(state, "{{")?;
            writeln!(
                state,
                "   {}::rust::exported_functions::{}({});",
                if func.sig.output.path.is_unit() { format!("{} oo; ", func.sig.output) } else { format!("{} oo = ", func.sig.output) },
                func.name,
                func.sig
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(n, ty)| {
                        format!("::rust::__zngur_internal_move_from_rust<{ty}>(i{n})")
                    })
                    .join(", "),
            )?;
            writeln!(state, "   ::rust::__zngur_internal_move_to_rust(o, oo);")?;
            writeln!(state, "}}")?;
        }
        for imp in &self.exported_impls {
            *is_really_needed = true;
            for (name, sig) in &imp.methods {
                sig.emit_link(&mut EmitMode::Cpp(state, state.hotreload), false)?;
                writeln!(state, "{{")?;
                writeln!(
                    state,
                    "   {}::rust::Impl<{}, {}>::{}({});",
                    if sig.output.path.is_unit() { format!("{} oo; ", sig.output) } else { format!("{} oo = ", sig.output) },
                    imp.ty,
                    match &imp.tr {
                        Some(x) => format!("{x}"),
                        None => "::rust::Inherent".to_string(),
                    },
                    name,
                    sig.inputs
                        .iter()
                        .enumerate()
                        .map(|(n, ty)| {
                            format!("::rust::__zngur_internal_move_from_rust<{ty}>(i{n})")
                        })
                        .join(", "),
                )?;
                writeln!(state, "   ::rust::__zngur_internal_move_to_rust(o, oo);")?;
                writeln!(state, "}}")?;
            }
        }
        writeln!(state, "}}")?;
        if state.hotreload {
            *is_really_needed = true;
            writeln!(state, "")?;
            writeln!(state, "ZngurCApi __zngur_get_capi() {{")?;
            writeln!(state, "   return ZngurCApi {{")?;
            for func in &self.exported_fn_defs {
                writeln!(state, "      .{0} = {0},", func.sig.rust_link_name)?;
            }
            for imp in &self.exported_impls {
                for (_, sig) in &imp.methods {
                    writeln!(state, "      .{0} = {0},", sig.rust_link_name)?;
                }
            }
            writeln!(state, "   }};")?;
            write!(state, "}}")?;
        }
        writeln!(state, "\n\n/* [Signatures]")?;
        SIG_OUTPUT.store(true, Ordering::SeqCst);
        for imp in &self.exported_impls {
            for (name, sig) in &imp.methods {
                writeln!(state,
                    "{} {}rust::Impl<{}, {}>::{}({})",
                    if sig.output.is_void() { "void".to_string() } else { format!("{}", sig.output) },
                    if !SIG_OUTPUT.load(Ordering::SeqCst) { "::" } else { "" },
                    imp.ty,
                    match &imp.tr {
                        Some(x) => format!("{x}"),
                        None => format!("{}rust::Inherent",
                            if !SIG_OUTPUT.load(Ordering::SeqCst) { "::" } else { "" }),
                    },
                    name,
                    sig.inputs
                        .iter()
                        .enumerate()
                        .map(|(n, ty)| format!("{ty} i{n}"))
                        .join(", "),
                )?;
            }
        }
        writeln!(state, "*/")?;
        SIG_OUTPUT.store(false, Ordering::SeqCst);
        Ok(())
    }

    pub fn render(self) -> (String, Option<String>) {
        #[cfg(feature="hotreload")]
        let hotreload = true;
        #[cfg(not(feature="hotreload"))]
        let hotreload = false;

        let mut h_file = State {
            text: "".to_owned(),
            panic_to_exception: self.panic_to_exception,
            hotreload,
            indent_count: 0,
            disable_ending_newline: false,
        };
        let mut cpp_file = State {
            text: "".to_owned(),
            panic_to_exception: self.panic_to_exception,
            hotreload,
            indent_count: 0,
            disable_ending_newline: false,
        };
        self.emit_h_file(&mut h_file).unwrap();
        let mut is_cpp_needed = false;
        self.emit_cpp_file(&mut cpp_file, &mut is_cpp_needed)
            .unwrap();
        (h_file.text, is_cpp_needed.then_some(cpp_file.text))
    }
}

pub fn cpp_handle_keyword(name: &str) -> &str {
    match name {
        "new" => "new_",
        "default" => "default_",
        x => x,
    }
}
