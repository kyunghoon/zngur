use std::collections::btree_map::Entry;
use std::collections::HashSet;

use cpp::sanitize_cpp_keywords;
use cpp::CppExportedFnDefinition;
use cpp::CppExportedImplDefinition;
use cpp::CppFile;
use cpp::CppFnDefinition;
use cpp::CppFnSig;
use cpp::CppMethod;
use cpp::CppPath;
use cpp::CppTraitDefinition;
use cpp::CppType;
use cpp::CppTypeDefinition;
use itertools::Itertools;
use rust::IntoCpp;

pub mod cpp;
mod rust;

pub use rust::RustFile;
pub use zngur_parser::ParsedZngFile;

pub use zngur_def::*;

pub struct ZngurGenerator(ZngurFile);

#[cfg(feature="hotreload")]
pub enum Signature {
    Function(String, String),
    WellKnown(String, String),
}

impl ZngurGenerator {
    pub fn build_from_zng(zng: ZngurFile) -> Self {
        ZngurGenerator(zng)
    }

    pub fn render(self) -> (String, String, Option<String>) {
        let zng = self.0;

        let owned_types = zng.types.iter().filter_map(|ty_def| match &ty_def.ty {
            RustType::Adt(RustPathAndGenerics { path, .. }) if ty_def.cpp_value.is_some() => Some(path.clone()),
            _ => None
        }).collect::<HashSet<_>>();

        let mut cpp_file = CppFile::default();
        cpp_file.additional_includes = zng.additional_includes;
        let mut rust_file = RustFile::default();
        cpp_file.trait_defs = zng
            .traits
            .iter()
            .map(|(key, value)| (key.clone(), rust_file.add_builder_for_dyn_trait(value)))
            .collect();
        if zng.convert_panic_to_exception {
            rust_file.enable_panic_to_exception();
            cpp_file.panic_to_exception = true;
        }
        for ty_def in zng.types {
            let is_copy = ty_def.wellknown_traits.contains(&ZngurWellknownTrait::Copy);
            match ty_def.layout {
                LayoutPolicy::StackAllocated { size, align } => {
                    rust_file.add_static_size_assert(&ty_def.ty, size);
                    rust_file.add_static_align_assert(&ty_def.ty, align);
                }
                LayoutPolicy::HeapAllocated => (),
                LayoutPolicy::OnlyByRef => (),
            }
            if is_copy {
                rust_file.add_static_is_copy_assert(&ty_def.ty);
            }
            let mut cpp_methods = vec![];
            let mut constructors = vec![];
            let mut alternates = vec![];
            let mut wellknown_traits = vec![];
            for constructor in ty_def.constructors {
                match constructor.name {
                    Some(name) => {
                        let rust_link_names = rust_file.add_constructor(
                            &format!("{}::{}", ty_def.ty, name),
                            &constructor.inputs,
                            ty_def.rust_value.as_ref(),
                        );
                        cpp_methods.push(CppMethod {
                            name: sanitize_cpp_keywords(&name).to_owned(),
                            kind: ZngurMethodReceiver::Static,
                            sig: CppFnSig {
                                rust_link_name: rust_link_names.constructor,
                                inputs: constructor.inputs.iter().map(|x| x.1.into_cpp()).collect(),
                                output: ty_def.ty.into_cpp(),
                            },
                        });
                        cpp_methods.push(CppMethod {
                            name: format!("matches_{}", name),
                            kind: ZngurMethodReceiver::Ref(Mutability::Not, None),
                            sig: CppFnSig {
                                rust_link_name: rust_link_names.match_check,
                                inputs: vec![ty_def.ty.into_cpp().into_ref()],
                                output: CppType::from("uint8_t"),
                            },
                        });
                        alternates.push(name);
                    }
                    None => {
                        let rust_link_name = rust_file
                            .add_constructor(&format!("{}", ty_def.ty), &constructor.inputs, ty_def.rust_value.as_ref())
                            .constructor;
                        constructors.push(CppFnSig {
                            rust_link_name,
                            inputs: constructor.inputs.iter().map(|x| x.1.into_cpp()).collect(),
                            output: ty_def.ty.into_cpp(),
                        });
                    }
                }
            }
            if let RustType::Tuple(fields) = &ty_def.ty {
                if !fields.is_empty() {
                    let rust_link_name = rust_file.add_tuple_constructor(&fields);
                    constructors.push(CppFnSig {
                        rust_link_name,
                        inputs: fields.iter().map(|x| x.into_cpp()).collect(),
                        output: ty_def.ty.into_cpp(),
                    });
                }
            }
            for wellknown_trait in ty_def.wellknown_traits {
                let data = rust_file.add_wellknown_trait(&ty_def.ty, wellknown_trait);
                wellknown_traits.push(data.clone());
            }
            for method_details in ty_def.methods {
                let ZngurMethodDetails {
                    data: method,
                    use_path,
                    deref,
                } = method_details;
                let (rusty_inputs, inputs) = real_inputs_of_method(&method, &ty_def.ty);
                let rust_link_name = rust_file.add_function(
                    method.receiver != ZngurMethodReceiver::Static,
                    &format!(
                        "<{}>::{}::<{}>",
                        deref.as_ref().unwrap_or(&ty_def.ty),
                        method.name,
                        method.generics.iter().join(", "),
                    ),
                    &rusty_inputs,
                    &method.output,
                    use_path,
                    deref.is_some(),
                );
                cpp_methods.push(CppMethod {
                    name: sanitize_cpp_keywords(&method.name).to_owned(),
                    kind: method.receiver,
                    sig: CppFnSig {
                        rust_link_name,
                        inputs,
                        output: method.output.into_cpp(),
                    },
                });
            }
            cpp_file.type_defs.push(CppTypeDefinition {
                ty: ty_def.ty.into_cpp(),
                layout: rust_file.add_layout_policy_shim(&ty_def.ty, ty_def.layout),
                constructors,
                alternates,
                methods: cpp_methods,
                wellknown_traits,
                cpp_value: ty_def.cpp_value.map(|(field, cpp_type)| {
                    let rust_link_name = rust_file.add_cpp_value_bridge(&ty_def.ty, &field);
                    (rust_link_name, cpp_type)
                }),
                cpp_ref: ty_def.cpp_ref,
                alias: ty_def.alias,
                from_trait: if let RustType::Boxed(b) = &ty_def.ty {
                    if let RustType::Dyn(tr, _) = b.as_ref() {
                        if let RustTrait::Fn {
                            name,
                            inputs,
                            output,
                        } = tr
                        {
                            if let Entry::Vacant(e) = cpp_file.trait_defs.entry(tr.clone()) {
                                let rust_link_name =
                                    rust_file.add_builder_for_dyn_fn(name, inputs, output);
                                e.insert(CppTraitDefinition::Fn {
                                    sig: CppFnSig {
                                        rust_link_name,
                                        inputs: inputs.iter().map(|x| x.into_cpp()).collect(),
                                        output: output.into_cpp(),
                                    },
                                });
                            }
                        }
                        Some(tr.clone())
                    } else {
                        None
                    }
                } else {
                    None
                },
                from_trait_ref: if let RustType::Dyn(tr, _) = &ty_def.ty {
                    Some(tr.clone())
                } else {
                    None
                },
            });
        }
        for func in zng.funcs {
            let rust_link_name = rust_file.add_function(
                func.has_receiver,
                &func.path.to_string(),
                &func.inputs,
                &func.output,
                None,
                false,
            );
            cpp_file.fn_defs.push(CppFnDefinition {
                name: CppPath::from_rust_path(&func.path.path),
                sig: CppFnSig {
                    rust_link_name,
                    inputs: func.inputs.into_iter().map(|x| x.into_cpp()).collect(),
                    output: func.output.into_cpp(),
                },
            });
        }
        for func in zng.extern_cpp_funcs {
            let rust_link_name =
                rust_file.add_extern_cpp_function(&func.name, &func.inputs, &func.output);
            cpp_file.exported_fn_defs.push(CppExportedFnDefinition {
                name: func.name.clone(),
                sig: CppFnSig {
                    rust_link_name,
                    inputs: func.inputs.into_iter().map(|x| x.into_cpp()).collect(),
                    output: func.output.into_cpp(),
                },
            });
        }
        for impl_block in zng.extern_cpp_impls {
            let rust_link_names = rust_file.add_extern_cpp_impl(
                &impl_block.ty,
                impl_block.tr.as_ref(),
                &impl_block.methods,
                &impl_block.lifetimes,
                &owned_types,
            );
            cpp_file.exported_impls.push(CppExportedImplDefinition {
                tr: impl_block.tr.map(|x| x.into_cpp()),
                ty: impl_block.ty.into_cpp(),
                methods: impl_block
                    .methods
                    .iter()
                    .zip(&rust_link_names)
                    .map(|(method, link_name)| {
                        let (_, inputs) = real_inputs_of_method(method, &impl_block.ty);
                        (
                            sanitize_cpp_keywords(&method.name).to_owned(),
                            CppFnSig {
                                rust_link_name: link_name.clone(),
                                inputs,
                                output: method.output.into_cpp(),
                            },
                        )
                    })
                    .collect(),
            });
        }

        #[cfg(feature="hotreload")]
        rust_file.add_hotload_api(&cpp_file);

        let (h, cpp) = cpp_file.render();
        (rust_file.text, h, cpp)
    }
}

fn real_inputs_of_method(method: &ZngurMethod, ty: &RustType) -> (Vec<RustType>, Vec<CppType>) {
    let receiver_type = match &method.receiver {
        ZngurMethodReceiver::Static => None,
        ZngurMethodReceiver::Ref(m, lt) => Some(RustType::Ref(*m, Box::new(ty.clone()), lt.clone())),
        ZngurMethodReceiver::Move => Some(ty.clone()),
    };
    let rusty_inputs = receiver_type
        .into_iter()
        .chain(method.inputs.clone())
        .collect::<Vec<_>>();
    let inputs = rusty_inputs.iter().map(|x| x.into_cpp()).collect_vec();
    (rusty_inputs, inputs)
}
