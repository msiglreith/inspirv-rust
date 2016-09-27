
use std::collections::HashMap;
use rustc::session::Session;
use syntax;
use syntax::ast::{LitKind, LitIntType, MetaItemKind, NestedMetaItemKind};
use inspirv::core::enumeration::*;
use inspirv_builder::module::Type;
use intrinsic::Intrinsic;

#[derive(Clone, Debug)]
pub enum Attribute {
    Interface,
    ConstBuffer,
    Location {
        location: u64,
    },
    Vector {
        base: Box<Type>,
        components: u64,
    },
    Matrix {
        base: Box<Type>,
        rows: u64,
        cols: u64,
    },
    EntryPoint {
        stage: ExecutionModel,
        execution_modes: HashMap<ExecutionModeKind, ExecutionMode>,
    },
    CompilerBuiltin,
    Builtin {
        builtin: BuiltIn
    },
    Intrinsic(Intrinsic),
    Descriptor {
        set: u64,
        binding: u64,
    },
}

pub fn parse(sess: &Session, ast_attribs: &[syntax::ast::Attribute]) -> Vec<Attribute> {
    let mut attrs = Vec::new();

    for attr in ast_attribs {
        match attr.node.value.node {
            MetaItemKind::List(ref name, ref items) if name == "inspirv" => {
                for item in items {
                    match item.node {
                        NestedMetaItemKind::MetaItem(ref item) => {
                            match item.node {
                                MetaItemKind::NameValue(ref name, ref value) => {
                                    match &**name {
                                        "entry_point" => {
                                            let stage = execution_model_from_str(&*extract_attr_str(value));
                                            if let Some(stage) = stage {
                                                attrs.push(Attribute::EntryPoint {
                                                    stage: stage,
                                                    execution_modes: HashMap::new(),
                                                });
                                            } else {
                                                sess.span_err(item.span, "Unknown `inspirv` entry_point execution model");
                                            }
                                        },
                                        "location" => {
                                            match value.node {
                                                LitKind::Int(b, LitIntType::Unsigned(..))
                                                | LitKind::Int(b, LitIntType::Unsuffixed) => attrs.push(Attribute::Location { location: b }),
                                                _ => panic!("attribute value need to be valid unsigned interger"),
                                            };
                                        },
                                        "builtin" => {
                                            let builtin = builtin_from_str(&*extract_attr_str(value));
                                            if let Some(builtin) = builtin {
                                                attrs.push(Attribute::Builtin { builtin: builtin });
                                            } else {
                                                sess.span_err(item.span, "Unknown `inspirv` builtin variable");
                                            }
                                        },

                                        _ => {
                                            sess.span_err(item.span, "Unknown `inspirv` attribute name value item")
                                        }
                                    }
                                },
                                MetaItemKind::Word(ref name) => {
                                    match &**name {
                                        "compiler_builtin" => attrs.push(Attribute::CompilerBuiltin),
                                        "interface" => attrs.push(Attribute::Interface),
                                        "const_buffer" => attrs.push(Attribute::ConstBuffer),
                                        _ => sess.span_err(item.span, "Unknown `inspirv`attribute word item"),
                                    }
                                },
                                MetaItemKind::List(ref name, ref items) => {
                                    match &**name {
                                        "vector" => {
                                            let mut base = None;
                                            let mut components = None;
                                            for item in items {
                                                match item.node {
                                                    NestedMetaItemKind::MetaItem(ref item) => {
                                                        match item.node {
                                                            MetaItemKind::NameValue(ref name, ref value) => {
                                                                match &**name {
                                                                    "components" => {
                                                                        components = match value.node {
                                                                            syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                            _ => panic!("attribute value needs to be interger (>2)"),
                                                                        }
                                                                    }
                                                                    "base" => {
                                                                        base = match &*extract_attr_str(value) {
                                                                            "bool" => Some(Type::Bool),
                                                                            "f32" => Some(Type::Float(32)),
                                                                            "f64" => Some(Type::Float(64)),

                                                                            _ => {
                                                                                sess.span_err(item.span, "Unsupported `inspirv` vector base type");
                                                                                None
                                                                            }
                                                                        }
                                                                    }
                                                                    _ => sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                                }
                                                            }
                                                            _ => sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                        }
                                                    }
                                                    _ => sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                }
                                            }

                                            if base.is_none() || components.is_none() {
                                                sess.span_err(item.span,
                                                                       "`inspirv` vector \
                                                                        misses `base` or \
                                                                        `component` \
                                                                        attributes");
                                            } else {
                                                attrs.push(Attribute::Vector { 
                                                    base: Box::new(base.unwrap()),
                                                    components: components.unwrap()
                                                });
                                            }
                                        }

                                        "matrix" => {
                                            let mut base = None;
                                            let mut rows = None;
                                            let mut cols = None;
                                            for item in items {
                                                match item.node {
                                                    NestedMetaItemKind::MetaItem(ref item) => {
                                                        match item.node {
                                                            MetaItemKind::NameValue(ref name, ref value) => {
                                                                match &**name {
                                                                    "rows" => {
                                                                        rows = match value.node {
                                                                            syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                            _ => panic!("attribute value needs to be interger (>2)"),
                                                                        }
                                                                    }
                                                                    "cols" => {
                                                                        cols = match value.node {
                                                                            syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                            _ => panic!("attribute value needs to be interger (>2)"),
                                                                        }
                                                                    }
                                                                    "base" => {
                                                                        base = match &*extract_attr_str(value) {
                                                                            "bool" => Some(Type::Bool),
                                                                            "f32" => Some(Type::Float(32)),
                                                                            "f64" => Some(Type::Float(64)),

                                                                            _ => {
                                                                                sess.span_err(item.span, "Unsupported `inspirv` matrix base type");
                                                                                None
                                                                            }
                                                                        }
                                                                    }
                                                                    _ => sess.span_err(item.span, "Unknown `inspirv` matrix attribute item"),
                                                                }
                                                            }
                                                            _ => sess.span_err(item.span, "Unknown `inspirv` matrix attribute item"),
                                                        }
                                                    }
                                                    _ => sess.span_err(item.span, "Unknown `inspirv` matrix attribute item"),
                                                }
                                            }

                                            if base.is_none() || rows.is_none() || cols.is_none() {
                                                sess.span_err(item.span, "`inspirv` matrix misses `base`, `rows` or `component` attributes");
                                            } else {
                                                attrs.push(Attribute::Matrix { 
                                                    base: Box::new(base.unwrap()),
                                                    rows: rows.unwrap(),
                                                    cols: cols.unwrap(),
                                                });
                                            }
                                        }

                                        "descriptor" => {
                                            let mut set = None;
                                            let mut binding = None;
                                            for item in items {
                                                match item.node {
                                                    NestedMetaItemKind::MetaItem(ref item) => {
                                                        match item.node {
                                                            MetaItemKind::NameValue(ref name, ref value) => {
                                                                match &**name {
                                                                    "set" => {
                                                                        set = match value.node {
                                                                            syntax::ast::LitKind::Int(b, _) => Some(b),
                                                                            _ => panic!("attribute value needs to be interger"),
                                                                        }
                                                                    },
                                                                    "binding" => {
                                                                        binding = match value.node {
                                                                            syntax::ast::LitKind::Int(b, _) => Some(b),
                                                                            _ => panic!("attribute value needs to be interger"),
                                                                        }
                                                                    },

                                                                    _ => sess.span_err(item.span, "Unknown `inspirv` descriptor attribute item"),
                                                                }
                                                            }
                                                            _ => sess.span_err(item.span, "Unknown `inspirv` descriptor attribute item"),
                                                        }
                                                    }
                                                    _ => sess.span_err(item.span, "Unknown `inspirv` descriptor attribute item"),
                                                }
                                            }

                                            if set.is_none() || binding.is_none() {
                                                sess.span_err(item.span, "`inspirv` descriptor misses `set` or `binding` attributes");
                                            } else {
                                                attrs.push(Attribute::Descriptor { 
                                                    set: set.unwrap(),
                                                    binding: binding.unwrap()
                                                });
                                            }
                                        }

                                        // intrinsics with additional data `instrinsic(name(..))` or `instrinsic(name)`
                                        "intrinsic" => {
                                            match items[0].node {
                                                NestedMetaItemKind::MetaItem(ref item) => {
                                                    match item.node {
                                                        MetaItemKind::List(ref name, ref items) => {
                                                            match &**name {
                                                                "shuffle" => {
                                                                    let mut num_components_in0 = None;
                                                                    let mut num_components_in1 = None;
                                                                    let mut num_components_out = None;
                                                                    for item in items {
                                                                        match item.node {
                                                                            NestedMetaItemKind::MetaItem(ref item) => {
                                                                                match item.node {
                                                                                    MetaItemKind::NameValue(ref name, ref value) => {
                                                                                        match &**name {
                                                                                            "num_in0" => {
                                                                                                num_components_in0 = match value.node {
                                                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b as u32),
                                                                                                    _ => panic!("attribute value needs to be interger (>2)"),
                                                                                                }
                                                                                            },
                                                                                            "num_in1" => {
                                                                                                num_components_in1 = match value.node {
                                                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b as u32),
                                                                                                    _ => panic!("attribute value needs to be interger (>2)"),
                                                                                                }
                                                                                            },
                                                                                            "num_out" => {
                                                                                                num_components_out = match value.node {
                                                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b as u32),
                                                                                                    _ => panic!("attribute value needs to be interger (>2)"),
                                                                                                }
                                                                                            },

                                                                                            _ => sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                                        }
                                                                                    }
                                                                                    _ => sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                                }
                                                                            }
                                                                            _ => sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                        }
                                                                    }
                                                                    if num_components_in0.is_none() ||
                                                                       num_components_in1.is_none() ||
                                                                       num_components_out.is_none() {
                                                                        sess.span_err(item.span, "`inspirv` shuffle misses `num_in0`, `num_in1` or `num_out` attributes");
                                                                    } else {
                                                                        let intrinsic = Intrinsic::Shuffle {
                                                                            components_out: num_components_out.unwrap(),
                                                                            components_in0: num_components_in0.unwrap(),
                                                                            components_in1: num_components_in1.unwrap(),
                                                                        };
                                                                        attrs.push(Attribute::Intrinsic(intrinsic));
                                                                    }
                                                                }
                                                                "swizzle" => {
                                                                    let mut num_components_in = None;
                                                                    let mut num_components_out = None;
                                                                    for item in items {
                                                                        match item.node {
                                                                            NestedMetaItemKind::MetaItem(ref item) => {
                                                                                match item.node {
                                                                                    MetaItemKind::NameValue(ref name, ref value) => {
                                                                                        match &**name {
                                                                                            "num_in" => {
                                                                                                num_components_in = match value.node {
                                                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b as u32),
                                                                                                    _ => panic!("attribute value needs to be interger (>2)"),
                                                                                                }
                                                                                            },
                                                                                            "num_out" => {
                                                                                                num_components_out = match value.node {
                                                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b as u32),
                                                                                                    _ => panic!("attribute value needs to be interger (>2)"),
                                                                                                }
                                                                                            },

                                                                                            _ => sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                                        }
                                                                                    }
                                                                                    _ => sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                                }
                                                                            }
                                                                            _ => sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                        }
                                                                    }
                                                                    if num_components_in.is_none() ||
                                                                       num_components_out.is_none() {
                                                                        sess.span_err(item.span, "`inspirv` swizzle misses `num_in` or `num_out` attributes");
                                                                    } else {
                                                                        let intrinsic = Intrinsic::Swizzle {
                                                                            components_out: num_components_out.unwrap(),
                                                                            components_in: num_components_in.unwrap(),
                                                                        };
                                                                        attrs.push(Attribute::Intrinsic(intrinsic));
                                                                    }
                                                                }
                                                                "vector_new" => {
                                                                    let mut components = Vec::new();
                                                                    for item in items {
                                                                        match item.node {
                                                                            NestedMetaItemKind::Literal(ref literal) => {
                                                                                match literal.node {
                                                                                    syntax::ast::LitKind::Int(b, _) => components.push(b as u32),
                                                                                    _ => panic!("attribute value needs to be interger"),
                                                                                }
                                                                            }
                                                                            _ => sess.span_err(item.span, "Unknown `inspirv` vector_new intrinsic attribute item"),
                                                                        }
                                                                    }
                                                                    if !components.is_empty() {
                                                                        let intrinsic = Intrinsic::VectorNew(components);
                                                                        attrs.push(Attribute::Intrinsic(intrinsic));
                                                                    } else {
                                                                        sess.span_err(item.span, "`inspirv` vector_new misses components attributes");
                                                                    }
                                                                }
                                                                _ => sess.span_err(item.span, "Unknown `inspirv` intrinsic"),
                                                            } 
                                                        }
                                                        MetaItemKind::Word(ref name) => {
                                                            match &**name {
                                                                _ => sess.span_err(item.span, "Unknown `inspirv` intrinsic"),
                                                            }
                                                        }
                                                        _ => sess.span_err(item.span, "Unknown `inspirv` intrinsic attribute item"),
                                                    }
                                                }
                                                _ => sess.span_err(items[0].span, "Unknown `inspirv` intrinsic attribute item"),
                                            }
                                        }
                                        _ => sess.span_err(item.span,
                                                                   "Unknown `inspirv` \
                                                                    attribute list item"),
                                    }  
                                },
                            }
                        },
                        _ => {
                            sess.span_err(item.span,
                                                   "Unknown `inspirv` attribute nested item.")
                        }
                    }
                }
            }

            // ignore non-`#[inspirv(..)]` attributes
            _ => (),
        }
    }

    attrs
}

fn execution_model_from_str(name: &str) -> Option<ExecutionModel> {
    use inspirv::core::enumeration::ExecutionModel::*;
    match name {
        "vertex" => Some(ExecutionModelVertex),
        "tessellation_control" => Some(ExecutionModelTessellationControl),
        "tessellation_eval" => Some(ExecutionModelTessellationEvaluation),
        "geometry" => Some(ExecutionModelGeometry),
        "fragment" => Some(ExecutionModelFragment),
        "compute" => Some(ExecutionModelGLCompute),
        "kernel" => Some(ExecutionModelKernel),
        _ => None,
    }
}

fn builtin_from_str(name: &str) -> Option<BuiltIn> {
    use inspirv::core::enumeration::BuiltIn::*;
    match name {
        // Should be all possible builtIn's for shaders 
        "Position" => Some(BuiltInPosition),
        "PointSize" => Some(BuiltInPointSize),
        "ClipDistance" => Some(BuiltInClipDistance),
        "CullDistance" => Some(BuiltInCullDistance),
        "VertexId" => Some(BuiltInVertexId),
        "InstanceId" => Some(BuiltInInstanceId),
        "PrimitiveId" => Some(BuiltInPrimitiveId),
        "Layer" => Some(BuiltInLayer),
        "InvocationId" => Some(BuiltInInvocationId),
        "ViewportIndex" => Some(BuiltInViewportIndex),
        "TessLevelOuter" => Some(BuiltInTessLevelOuter),
        "TessLevelInner" => Some(BuiltInTessLevelInner),
        "TessCoord" => Some(BuiltInTessCoord),
        "PatchVertices" => Some(BuiltInPatchVertices),
        "FragCoord" => Some(BuiltInFragCoord),
        "PointCoord" => Some(BuiltInPointCoord),
        "FrontFacing" => Some(BuiltInFrontFacing),
        "SampleId" => Some(BuiltInSampleId),
        "SamplePosition" => Some(BuiltInSamplePosition),
        "SampleMask" => Some(BuiltInSampleMask),
        "FragDepth" => Some(BuiltInFragDepth),
        "HelperInvocation" => Some(BuiltInHelperInvocation),
        "NumWorkgroups" => Some(BuiltInNumWorkgroups),
        "WorkgroupSize" => Some(BuiltInWorkgroupSize),
        "WorkgroupId" => Some(BuiltInWorkgroupId),
        "LocalInvocationId" => Some(BuiltInLocalInvocationId),
        "GlobalInvocationId" => Some(BuiltInGlobalInvocationId),
        "LocalInvocationIndex" => Some(BuiltInLocalInvocationIndex),
        "VertexIndex" => Some(BuiltInVertexIndex),
        "InstanceIndex" => Some(BuiltInInstanceIndex),
        _ => None,
    }
}

fn extract_attr_str(lit: &syntax::ast::Lit) -> syntax::parse::token::InternedString {
    match lit.node {
        syntax::ast::LitKind::Str(ref s, _) => s.clone(),
        _ => panic!("attribute values need to be strings"),
    }
}
