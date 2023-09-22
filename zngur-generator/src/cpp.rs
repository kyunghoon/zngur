use std::{
    collections::HashMap,
    fmt::{Display, Write},
};

use iter_tools::Itertools;
use zngur_def::{LayoutPolicy, RustTrait};

use crate::{rust::IntoCpp, ZngurWellknownTraitData};

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
        for p in self.namespace() {
            writeln!(state, "namespace {} {{", p)?;
        }
        f(state)?;
        for _ in self.namespace() {
            writeln!(state, "}}")?;
        }
        Ok(())
    }

    fn name(&self) -> &str {
        self.0.split_last().unwrap().0
    }

    fn need_header(&self) -> bool {
        self.0.first().map(|x| x.as_str()) == Some("rust") && self.0 != ["rust", "Unit"]
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "::{}", self.0.iter().join("::"))
    }
}

#[derive(Debug)]
pub struct CppType {
    pub path: CppPath,
    pub generic_args: Vec<CppType>,
}

impl CppType {
    pub fn into_ref(self) -> CppType {
        CppType {
            path: CppPath::from("rust::Ref"),
            generic_args: vec![self],
        }
    }

    fn emit_specialization_decl(&self, state: &mut State) -> std::fmt::Result {
        if self.generic_args.is_empty() {
            write!(state, "struct {}", self.path.name())?;
        } else {
            write!(
                state,
                "template<> struct {}<{}>",
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
        self.path.emit_in_namespace(state, |state| {
            if !self.generic_args.is_empty() {
                writeln!(
                    state,
                    "template<{}>",
                    (0..self.generic_args.len())
                        .map(|n| format!("typename T{n}"))
                        .join(", ")
                )?;
            }
            writeln!(state, "struct {};", self.path.name())
        })
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
        match value.split_once("<") {
            None => CppType {
                path: CppPath::from(value),
                generic_args: vec![],
            },
            Some((path, generics)) => {
                let generics = generics.strip_suffix(">").unwrap();
                CppType {
                    path: CppPath::from(path),
                    generic_args: split_string(generics).map(|x| CppType::from(&*x)).collect(),
                }
            }
        }
    }
}

struct State {
    text: String,
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

#[derive(Debug)]
pub struct CppFnSig {
    pub rust_link_name: String,
    pub inputs: Vec<CppType>,
    pub output: CppType,
}

impl CppFnSig {
    fn emit_rust_link(&self, state: &mut State) -> std::fmt::Result {
        write!(state, "void {}(", self.rust_link_name)?;
        for n in 0..self.inputs.len() {
            write!(state, "uint8_t* i{n},")?;
        }
        write!(state, "uint8_t* o)")?;
        Ok(())
    }

    fn emit_rust_link_decl(&self, state: &mut State) -> std::fmt::Result {
        self.emit_rust_link(state)?;
        writeln!(state, ";")?;
        Ok(())
    }

    fn emit_cpp_header(&self, state: &mut State, fn_name: &str) -> std::fmt::Result {
        let CppFnSig {
            inputs,
            output,
            rust_link_name: _,
        } = self;
        writeln!(
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
        let CppFnSig {
            inputs,
            output,
            rust_link_name,
        } = self;
        writeln!(
            state,
            "inline {output} {fn_name}({input_defs})
        {{
            {output} o;
            ::rust::__zngur_internal_assume_init(o);
            {rust_link_name}({input_args}::rust::__zngur_internal_data_ptr(o));
            {deinits}
            return o;
        }}",
            input_defs = inputs
                .iter()
                .enumerate()
                .map(|(n, ty)| format!("{ty} i{n}"))
                .join(", "),
            input_args = (0..inputs.len())
                .map(|n| format!("::rust::__zngur_internal_data_ptr(i{n}), "))
                .join(""),
            deinits = (0..inputs.len())
                .map(|n| format!("::rust::__zngur_internal_assume_deinit(i{n});"))
                .join("\n"),
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

#[derive(PartialEq, Eq, Hash)]
pub enum CppMethodKind {
    StaticOnly,
    Lvalue,
    Rvalue,
}

pub struct CppMethod {
    pub name: String,
    pub kind: CppMethodKind,
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
    fn emit_rust_links(&self, state: &mut State) -> std::fmt::Result {
        match self {
            CppTraitDefinition::Fn {
                sig:
                    CppFnSig {
                        rust_link_name,
                        inputs: _,
                        output: _,
                    },
            } => {
                // TODO: too special
                writeln!(
                    state,
                    "void {rust_link_name}(uint8_t *data, void destructor(uint8_t *),
                void call(uint8_t *, uint8_t *, uint8_t *),
                uint8_t *o);"
                )?;
            }
            CppTraitDefinition::Normal {
                link_name,
                link_name_ref,
                ..
            } => {
                writeln!(
                    state,
                    "void {link_name}(uint8_t *data, void destructor(uint8_t *), uint8_t *o);"
                )?;
                writeln!(state, "void {link_name_ref}(uint8_t *data, uint8_t *o);")?;
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
        virtual ~{}() {{}}
    "#,
                as_ty.path.name(),
            )?;
            for method in methods {
                write!(
                    state,
                    r#"
            virtual {output} {name}({input}) = 0;
    "#,
                    output = method.output,
                    name = method.name,
                    input = method
                        .inputs
                        .iter()
                        .enumerate()
                        .map(|(n, x)| format!("{x} i{n}"))
                        .join(", "),
                )?;
            }
            write!(
                state,
                r#"
    }};
    "#,
            )
        })
    }

    fn emit_cpp(&self, state: &mut State) -> std::fmt::Result {
        match self {
            CppTraitDefinition::Fn { .. } => (),
            CppTraitDefinition::Normal {
                as_ty,
                methods,
                link_name,
                link_name_ref,
            } => {
                for method in dbg!(methods) {
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

pub struct CppTypeDefinition {
    pub ty: CppType,
    pub layout: LayoutPolicy,
    pub methods: Vec<CppMethod>,
    pub constructors: Vec<CppFnSig>,
    pub from_trait: Option<RustTrait>,
    pub from_trait_ref: Option<RustTrait>,
    pub wellknown_traits: Vec<ZngurWellknownTraitData>,
    pub cpp_value: Option<(String, String)>,
    pub cpp_ref: Option<String>,
}

impl Default for CppTypeDefinition {
    fn default() -> Self {
        Self {
            ty: CppType::from("fill::me::you::forgot::it"),
            layout: LayoutPolicy::OnlyByRef,
            methods: vec![],
            constructors: vec![],
            wellknown_traits: vec![],
            from_trait: None,
            from_trait_ref: None,
            cpp_value: None,
            cpp_ref: None,
        }
    }
}

impl CppTypeDefinition {
    fn emit_ref_specialization(&self, state: &mut State) -> std::fmt::Result {
        let is_unsized = self
            .wellknown_traits
            .contains(&ZngurWellknownTraitData::Unsized);
        if is_unsized {
            writeln!(
                state,
                r#"
template<>
struct rust::Ref<{ty}> {{
    Ref() {{
        data = {{0, 0}};
    }}
private:
    ::std::array<size_t, 2> data;
    friend uint8_t* ::rust::__zngur_internal_data_ptr<::rust::Ref<{ty}>>(::rust::Ref<{ty}>& t);
"#,
                ty = self.ty,
            )?;
        } else {
            writeln!(
                state,
                r#"
template<>
struct rust::Ref<{ty}> {{
    Ref() {{
        data = 0;
    }}
    Ref({ty}& t) {{
        data = (size_t)__zngur_internal_data_ptr(t);
    }}
private:
    size_t data;
    friend uint8_t* ::rust::__zngur_internal_data_ptr<::rust::Ref<{ty}>>(::rust::Ref<{ty}>& t);
"#,
                ty = self.ty,
            )?;
        }
        writeln!(state, "public:")?;
        match &self.from_trait_ref {
            Some(RustTrait::Fn { inputs, output, .. }) => {
                let as_std_function = format!(
                    "::std::function<{}({})>",
                    output.into_cpp(),
                    inputs.iter().map(|x| x.into_cpp()).join(", ")
                );
                writeln!(
                    state,
                    r#"
static inline {ty} build({as_std_function} f);
"#,
                    ty = self.ty.path.name(),
                )?;
            }
            Some(tr @ RustTrait::Normal { .. }) => {
                let tr = tr.into_cpp();
                writeln!(
                    state,
                    r#"
            static inline Ref build({tr}& arg);
            "#,
                )?;
            }
            None => (),
        }
        if let Some((rust_link_name, cpp_ty)) = &self.cpp_value {
            writeln!(
                state,
                r#"
                inline {cpp_ty}& cpp() {{
                    return (*{rust_link_name}((uint8_t*)data)).as_cpp<{cpp_ty}>();
                }}"#
            )?;
        }
        if let Some(cpp_ty) = &self.cpp_ref {
            writeln!(
                state,
                r#"
                inline {cpp_ty}& cpp() {{
                    return *({cpp_ty}*)data;
                }}"#
            )?;
            writeln!(
                state,
                r#"
                inline static Ref build(const {cpp_ty}& t) {{
                    Ref o;
                    o.data = (size_t)&t;
                    return o;
                }}"#
            )?;
        }
        for method in &self.methods {
            if method.kind == CppMethodKind::Lvalue {
                let CppFnSig {
                    rust_link_name: _,
                    inputs,
                    output,
                } = &method.sig;
                writeln!(
                    state,
                    "{output} {fn_name}({input_defs});",
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
        if self.ty.path.to_string() == "::rust::Str" {
            writeln!(
                state,
                r#"
    friend rust::Str;
}};
inline ::rust::Ref<::rust::Str> rust::Str::from_char_star(const char* s) {{
    ::rust::Ref<::rust::Str> o;
    o.data[0] = (size_t)s;
    o.data[1] = strlen(s);
    return o;
}}
"#,
            )?;
        } else {
            writeln!(state, "}};")?;
        }
        writeln!(
            state,
            r#"
namespace rust {{

template<>
inline uint8_t* __zngur_internal_data_ptr<Ref<{ty}>>(Ref<{ty}>& t) {{
    return (uint8_t*)&t.data;
}}

template<>
inline void __zngur_internal_assume_init<Ref<{ty}>>(Ref<{ty}>&) {{
}}

template<>
inline void __zngur_internal_check_init<Ref<{ty}>>(Ref<{ty}>&) {{
}}

template<>
inline void __zngur_internal_assume_deinit<Ref<{ty}>>(Ref<{ty}>&) {{
}}

template<>
inline size_t __zngur_internal_size_of<Ref<{ty}>>() {{
    return {size};
}}
}}"#,
            ty = self.ty,
            size = if is_unsized { 16 } else { 8 },
        )?;
        Ok(())
    }

    fn emit(&self, state: &mut State) -> std::fmt::Result {
        let is_copy = self
            .wellknown_traits
            .contains(&ZngurWellknownTraitData::Copy);
        writeln!(
            state,
            r#"
namespace rust {{
    template<>
    inline uint8_t* __zngur_internal_data_ptr<{ty}>({ty}& t);
    template<>
    inline void __zngur_internal_check_init<{ty}>({ty}& t);
    template<>
    inline void __zngur_internal_assume_init<{ty}>({ty}& t);
    template<>
    inline void __zngur_internal_assume_deinit<{ty}>({ty}& t);
    template<>
    inline size_t __zngur_internal_size_of<{ty}>();
}}"#,
            ty = self.ty,
        )?;
        self.ty.path.emit_in_namespace(state, |state| {
            if self.ty.path.0 == ["rust", "Unit"] {
                write!(state, "template<> struct Tuple<> {{ uint8_t data; }};")?;
                return Ok(());
            } else {
                self.ty.emit_specialization_decl(state)?;
            }
            match self.layout {
                LayoutPolicy::HeapAllocated | LayoutPolicy::OnlyByRef => {
                    writeln!(
                        state,
                        r#"
{{
public:
    {ty}() = delete;
    "#,
                        ty = self.ty.path.name(),
                    )?;
                    if self.ty.path.to_string() == "::rust::Str" {
                        writeln!(
                            state,
                            r#"
    static inline ::rust::Ref<::rust::Str> from_char_star(const char* s);
    "#,
                        )?;
                    }
                }
                LayoutPolicy::StackAllocated { size, align } => {
                    writeln!(
                        state,
                        r#"
{{
private:
    alignas({align}) ::std::array<uint8_t, {size}> data;
    friend uint8_t* ::rust::__zngur_internal_data_ptr<{ty}>({ty}& t);
    friend void ::rust::__zngur_internal_check_init<{ty}>({ty}& t);
    friend void ::rust::__zngur_internal_assume_init<{ty}>({ty}& t);
    friend void ::rust::__zngur_internal_assume_deinit<{ty}>({ty}& t);
    friend void ::rust::zngur_pretty_print<{ty}>({ty}& t);
"#,
                        ty = self.ty,
                    )?;
                    if self.ty.path.to_string() == "::rust::Bool" {
                        assert_eq!(size, 1);
                        assert_eq!(align, 1);
                        assert!(is_copy);
                        writeln!(
                            state,
                            r#"
public:
    operator bool() {{
        return data[0];
    }}
    Bool(bool b) {{
        data[0] = b;
    }}
private:
    "#,
                        )?;
                    }
                    if !is_copy {
                        writeln!(state, "   bool drop_flag;")?;
                    }
                    writeln!(state, "public:")?;
                    if is_copy {
                        writeln!(
                            state,
                            r#"
    {ty}() {{}}
    ~{ty}() {{}}
    {ty}(const {ty}& other) : data(other.data) {{}}
    {ty}& operator=(const {ty}& other) {{
        this->data = other.data;
        return *this;
    }}
    {ty}({ty}&& other) : data(other.data) {{}}
    {ty}& operator=({ty}&& other) {{
        this->data = other.data;
        return *this;
    }}
    "#,
                            ty = self.ty.path.name(),
                        )?;
                    } else {
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
                        writeln!(
                            state,
                            r#"
    {ty}() : drop_flag(false) {{}}
    ~{ty}() {{
        if (drop_flag) {{
            {drop_in_place}(&data[0]);
        }}
    }}
    {ty}(const {ty}& other) = delete;
    {ty}& operator=(const {ty}& other) = delete;
    {ty}({ty}&& other) : drop_flag(false) {{
        *this = ::std::move(other);
    }}
    {ty}& operator=({ty}&& other) {{
        if (this != &other)
        {{
            if (drop_flag) {{
                {drop_in_place}(&data[0]);
            }}
            this->drop_flag = other.drop_flag;
            this->data = other.data;
            other.drop_flag = false;
        }}
        return *this;
    }}
    "#,
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
                            writeln!(
                                state,
                                r#"
    static inline {ty} build({as_std_function} f);
    "#,
                                ty = self.ty.path.name(),
                            )?;
                        }
                        Some(RustTrait::Normal { .. }) => {
                            writeln!(
                                state,
                                r#"
                        template<typename T, typename... Args>
                        static {ty} make_box(Args&&... args);
                        "#,
                                ty = self.ty.path.name(),
                            )?;
                        }
                        None => (),
                    }
                }
            }
            if let Some((rust_link_name, cpp_ty)) = &self.cpp_value {
                writeln!(
                    state,
                    r#"
                    inline {cpp_ty}& cpp() {{
                        return (*{rust_link_name}((uint8_t*)&data[0])).as_cpp<{cpp_ty}>();
                    }}"#
                )?;
            }
            for method in &self.methods {
                write!(state, "static ")?;
                method.sig.emit_cpp_header(state, &method.name)?;
                if method.kind != CppMethodKind::StaticOnly {
                    let CppFnSig {
                        rust_link_name: _,
                        inputs,
                        output,
                    } = &method.sig;
                    writeln!(
                        state,
                        "{output} {fn_name}({input_defs});",
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
            for constructor in &self.constructors {
                writeln!(
                    state,
                    "{fn_name}({input_defs});",
                    fn_name = &self.ty.path.0.last().unwrap(),
                    input_defs = constructor
                        .inputs
                        .iter()
                        .enumerate()
                        .map(|(n, ty)| format!("{ty} i{n}"))
                        .join(", "),
                )?;
            }
            writeln!(state, "}};")
        })?;
        let ty = &self.ty;
        if let LayoutPolicy::StackAllocated { size, .. } = self.layout {
            writeln!(
                state,
                r#"
namespace rust {{
    template<>
    inline size_t __zngur_internal_size_of<{ty}>() {{
        return {size};
    }}
"#,
            )?;
            if is_copy {
                writeln!(
                    state,
                    r#"
        template<>
        inline void __zngur_internal_check_init<{ty}>({ty}&) {{
        }}

        template<>
        inline void __zngur_internal_assume_init<{ty}>({ty}&) {{
        }}
    
        template<>
        inline void __zngur_internal_assume_deinit<{ty}>({ty}&) {{
        }}
"#,
                )?;
            } else {
                writeln!(
                    state,
                    r#"
        template<>
        inline void __zngur_internal_check_init<{ty}>({ty}& t) {{
            if (!t.drop_flag) {{
                ::std::cerr << "Use of uninitialized or moved Zngur Rust object with type {ty}" << ::std::endl;
                while (true) raise(SIGSEGV);
            }}
        }}

        template<>
        inline void __zngur_internal_assume_init<{ty}>({ty}& t) {{
            t.drop_flag = true;
        }}
    
        template<>
        inline void __zngur_internal_assume_deinit<{ty}>({ty}& t) {{
            t.drop_flag = false;
        }}
"#,
                )?;
            }
            writeln!(
                state,
                r#"
    template<>
    inline uint8_t* __zngur_internal_data_ptr<{ty}>({ty}& t) {{
        ::rust::__zngur_internal_check_init<{ty}>(t);
        return (uint8_t*)&t.data;
    }}
}}
"#,
            )?;
        }
        self.emit_ref_specialization(state)
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
        for c in &self.constructors {
            let fn_name = my_name.to_owned() + "::" + &self.ty.path.0.last().unwrap();
            let CppFnSig {
                inputs,
                output: _,
                rust_link_name,
            } = c;
            writeln!(
                state,
                "inline {fn_name}({input_defs})
        {{
            ::rust::__zngur_internal_assume_init(*this);
            {rust_link_name}({input_args}::rust::__zngur_internal_data_ptr(*this));
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
                deinits = (0..inputs.len())
                    .map(|n| format!("::rust::__zngur_internal_assume_deinit(i{n});"))
                    .join("\n"),
            )?;
        }
        match self.from_trait.as_ref().and_then(|k| traits.get(&k)) {
            Some(CppTraitDefinition::Fn { sig }) => {
                // TODO: too special
                let as_std_function = format!(
                    "::std::function<{}({})>",
                    sig.output,
                    sig.inputs.iter().join(", ")
                );
                let ii_args = sig
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(n, x)| format!("{x} ii{n} = *({x} *)i{n};"))
                    .join("\n");
                writeln!(
                    state,
                    r#"
{my_name} {my_name}::build({as_std_function} f) {{
auto data = new {as_std_function}(f);
{my_name} o;
::rust::__zngur_internal_assume_init(o);
{link_name}(
(uint8_t *)data,
[](uint8_t *d) {{ delete ({as_std_function} *)d; }},
[](uint8_t *d, uint8_t *i0, uint8_t *o) {{
int32_t *oo = (int32_t *)o;
{ii_args}
auto dd = ({as_std_function} *)d;
*oo = (*dd)(ii0);
}},
::rust::__zngur_internal_data_ptr(o));
return o;
}}
"#,
                    link_name = sig.rust_link_name,
                )?;
            }
            Some(CppTraitDefinition::Normal {
                as_ty,
                methods,
                link_name,
                link_name_ref: _,
            }) => {
                writeln!(
                    state,
                    r#"
template<typename T, typename... Args>
{my_name} {my_name}::make_box(Args&&... args) {{
auto data = new T(::std::forward<Args>(args)...);
auto data_as_impl = dynamic_cast<{as_ty}*>(data);
{my_name} o;
::rust::__zngur_internal_assume_init(o);
{link_name}(
(uint8_t *)data_as_impl,
[](uint8_t *d) {{ delete ({as_ty} *)d; }},
"#,
                )?;
                writeln!(
                    state,
                    r#"
::rust::__zngur_internal_data_ptr(o));
return o;
}}
"#,
                )?;
            }
            None => (),
        }
        match self.from_trait_ref.as_ref().and_then(|k| traits.get(&k)) {
            Some(CppTraitDefinition::Fn { sig }) => {
                todo!()
            }
            Some(CppTraitDefinition::Normal {
                as_ty,
                methods,
                link_name: _,
                link_name_ref,
            }) => {
                writeln!(
                    state,
                    r#"
rust::Ref<{my_name}> rust::Ref<{my_name}>::build({as_ty}& args) {{
auto data_as_impl = &args;
rust::Ref<{my_name}> o;
::rust::__zngur_internal_assume_init(o);
{link_name_ref}(
(uint8_t *)data_as_impl,
"#,
                )?;
                writeln!(
                    state,
                    r#"
::rust::__zngur_internal_data_ptr(o));
return o;
}}
"#,
                )?;
            }
            None => (),
        }
        for method in &self.methods {
            let fn_name = my_name.to_owned() + "::" + &method.name;
            method.sig.emit_cpp_def(state, &fn_name)?;
            if method.kind == CppMethodKind::Lvalue {
                let CppFnSig {
                    rust_link_name: _,
                    inputs,
                    output,
                } = &method.sig;
                writeln!(
                    state,
                    "inline {output} rust::Ref<{ty}>::{method_name}({input_defs})
                {{
                    return {fn_name}(*this{input_args});
                }}",
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
            if !is_unsized && method.kind != CppMethodKind::StaticOnly {
                let CppFnSig {
                    rust_link_name: _,
                    inputs,
                    output,
                } = &method.sig;
                writeln!(
                    state,
                    "inline {output} {fn_name}({input_defs})
                {{
                    return {fn_name}({this_arg}{input_args});
                }}",
                    this_arg = match method.kind {
                        CppMethodKind::Lvalue => "*this",
                        CppMethodKind::Rvalue => "::std::move(*this)",
                        CppMethodKind::StaticOnly => unreachable!(),
                    },
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
        for tr in &self.wellknown_traits {
            match tr {
                ZngurWellknownTraitData::Debug {
                    pretty_print,
                    debug_print: _, // TODO: use it
                } => {
                    writeln!(
                        state,
                        r#"
            namespace rust {{
                template<>
                inline void zngur_pretty_print<{ty}>({ty}& t) {{
                    ::rust::__zngur_internal_check_init<{ty}>(t);
                    {pretty_print}((uint8_t*)&t.data);
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

    fn emit_rust_links(&self, state: &mut State) -> std::fmt::Result {
        for method in &self.methods {
            method.sig.emit_rust_link_decl(state)?;
        }
        for c in &self.constructors {
            c.emit_rust_link_decl(state)?;
        }
        if let Some(cpp_value) = &self.cpp_value {
            writeln!(
                state,
                "::rust::ZngurCppOpaqueOwnedObject* {}(uint8_t*);",
                cpp_value.0
            )?;
        }
        for tr in &self.wellknown_traits {
            match tr {
                ZngurWellknownTraitData::Debug {
                    pretty_print,
                    debug_print,
                } => {
                    writeln!(state, "void {pretty_print}(uint8_t *data);")?;
                    writeln!(state, "void {debug_print}(uint8_t *data);")?;
                }
                ZngurWellknownTraitData::Unsized | ZngurWellknownTraitData::Copy => (),
                ZngurWellknownTraitData::Drop { drop_in_place } => {
                    writeln!(state, "void {drop_in_place}(uint8_t *data);")?;
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
}

impl CppFile {
    fn emit_h_file(&self, state: &mut State) -> std::fmt::Result {
        state.text += &self.additional_includes;
        state.text += r#"
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <csignal>
#include <array>
#include <iostream>
#include <functional>
#include <math.h>

#define zngur_dbg(x)                                                           \
  {                                                                            \
    ::std::cerr << "[" << __FILE__ << ":" << __LINE__ << "] " << #x << " = ";  \
    ::rust::zngur_pretty_print(x);                                             \
  }

namespace rust {
    template<typename T>
    uint8_t* __zngur_internal_data_ptr(T& t);

    template<typename T>
    void __zngur_internal_assume_init(T& t);

    template<typename T>
    void __zngur_internal_assume_deinit(T& t);

    template<typename T>
    inline size_t __zngur_internal_size_of();

    template<typename T>
    inline void __zngur_internal_move_to_rust(uint8_t* dst, T& t) {
        memcpy(dst, ::rust::__zngur_internal_data_ptr(t), ::rust::__zngur_internal_size_of<T>());
        ::rust::__zngur_internal_assume_deinit(t);
    }

    template<typename T>
    inline T __zngur_internal_move_from_rust(uint8_t* src) {
        T t;
        ::rust::__zngur_internal_assume_init(t);
        memcpy(::rust::__zngur_internal_data_ptr(t), src, ::rust::__zngur_internal_size_of<T>());
        return t;
    }

    template<typename T>
    inline void __zngur_internal_check_init(T& t) {
    }

    class ZngurCppOpaqueOwnedObject {
        uint8_t* data;
        void (*destructor)(uint8_t*);

    public:
        template<typename T, typename... Args>
        inline static ZngurCppOpaqueOwnedObject build(Args&&... args) {
            ZngurCppOpaqueOwnedObject o;
            o.data = (uint8_t*) new T(::std::forward<Args>(args)...);
            o.destructor = [](uint8_t* d) {
                delete (T*)d;
            };
            return o;
        }

        template<typename T>
        inline T& as_cpp() {
            return *(T *)data;
        }
    };

    template<typename T>
    struct Ref;

    template<typename... T>
    struct Tuple;

    using Unit = Tuple<>;

    template<typename T>
    void zngur_pretty_print(T&) {}

    class Inherent;

    template<typename Type, typename Trait = Inherent>
    class Impl;
"#;
        for ty in [8, 16, 32, 64]
            .into_iter()
            .flat_map(|x| [format!("int{x}_t"), format!("uint{x}_t")])
            .chain([
                format!("::rust::ZngurCppOpaqueOwnedObject"),
                format!("::double_t"),
                format!("::float_t"),
            ])
        {
            writeln!(
                state,
                r#"
    template<>
    inline uint8_t* __zngur_internal_data_ptr<{ty}>({ty}& t) {{
        return (uint8_t*)&t;
    }}

    template<>
    inline void __zngur_internal_assume_init<{ty}>({ty}&) {{}}
    template<>
    inline void __zngur_internal_assume_deinit<{ty}>({ty}&) {{}}

    template<>
    inline size_t __zngur_internal_size_of<{ty}>() {{
        return sizeof({ty});
    }}

    template<>
    inline uint8_t* __zngur_internal_data_ptr<{ty}*>({ty}*& t) {{
        return (uint8_t*)&t;
    }}

    template<>
    inline void __zngur_internal_assume_init<{ty}*>({ty}*&) {{}}
    template<>
    inline void __zngur_internal_assume_deinit<{ty}*>({ty}*&) {{}}

    template<>
    struct Ref<{ty}> {{
        Ref() {{
            data = 0;
        }}
        Ref({ty}& t) {{
            data = (size_t)__zngur_internal_data_ptr(t);
        }}

        {ty}& operator*() {{
            return *({ty}*)data;
        }}
        private:
            size_t data;
        friend uint8_t* ::rust::__zngur_internal_data_ptr<Ref<{ty}>>(::rust::Ref<{ty}>& t);
    }};
"#
            )?;
        }
        writeln!(state, "}}")?;
        writeln!(state, "extern \"C\" {{")?;
        for f in &self.fn_defs {
            f.sig.emit_rust_link_decl(state)?;
        }
        for td in &self.type_defs {
            td.emit_rust_links(state)?;
        }
        for (_, td) in &self.trait_defs {
            td.emit_rust_links(state)?;
        }
        writeln!(state, "}}")?;
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
            writeln!(state, "namespace rust {{ namespace exported_functions {{")?;
            write!(state, "   {} {}(", func.sig.output, func.name)?;
            for (n, ty) in func.sig.inputs.iter().enumerate() {
                if n != 0 {
                    write!(state, ", ")?;
                }
                write!(state, "{ty} i{n}")?;
            }
            writeln!(state, ");")?;
            writeln!(state, "}} }}")?;
        }
        for imp in &self.exported_impls {
            writeln!(
                state,
                "namespace rust {{ template<> class Impl<{}, {}> {{ public:",
                imp.ty,
                match &imp.tr {
                    Some(x) => format!("{x}"),
                    None => format!("::rust::Inherent"),
                }
            )?;
            for (name, sig) in &imp.methods {
                write!(state, "   static {} {}(", sig.output, name)?;
                for (n, ty) in sig.inputs.iter().enumerate() {
                    if n != 0 {
                        write!(state, ", ")?;
                    }
                    write!(state, "{ty} i{n}")?;
                }
                writeln!(state, ");")?;
            }
            writeln!(state, "}}; }}")?;
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
            func.sig.emit_rust_link(state)?;
            writeln!(state, "{{")?;
            writeln!(
                state,
                "   {} oo = ::rust::exported_functions::{}({});",
                func.sig.output,
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
                sig.emit_rust_link(state)?;
                writeln!(state, "{{")?;
                writeln!(
                    state,
                    "   {} oo = ::rust::Impl<{}, {}>::{}({});",
                    sig.output,
                    imp.ty,
                    match &imp.tr {
                        Some(x) => format!("{x}"),
                        None => format!("::rust::Inherent"),
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
        Ok(())
    }

    pub fn render(self) -> (String, Option<String>) {
        let mut h_file = State {
            text: "".to_owned(),
        };
        let mut cpp_file = State {
            text: "".to_owned(),
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
