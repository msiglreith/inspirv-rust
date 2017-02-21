
use std::collections::HashMap;
use rustc::session::Session;
use rustc::hir;
use rustc::hir::def_id::DefId;
use syntax;
use syntax::ast::{LitKind, LitIntType, MetaItemKind, NestedMetaItemKind};
use syntax::symbol::InternedString;
use inspirv::core::enumeration::*;
use intrinsic::Intrinsic;
use error::{PResult, DiagnosticBuilderExt};
use context::CrateContext;

#[derive(Clone, Debug)]
pub enum Attribute {
    Interface,
    ConstBuffer,
    Location {
        location: u64,
    },
    Vector {
        components: u64,
    },
    Matrix {
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

pub fn attributes<'a, 'tcx: 'a>(cx: &'a CrateContext<'a, 'tcx>, def_id: DefId) -> Vec<Attribute> {
    let attrs = cx.tcx().get_attrs(def_id);
    match parse(cx.sess(), &attrs) {
        Ok(attrs) => attrs,
        Err(mut err) => {
            err.emit();
            Vec::new()
        }
    }
}

pub fn struct_field_attributes<'a, 'tcx: 'a>(
        cx: &'a CrateContext<'a, 'tcx>,
        struct_id: DefId,
        field_id: DefId) -> Vec<Attribute> {
    let tcx = cx.tcx();
    let (item, field_id) = if let Some(struct_id) = tcx.hir.as_local_node_id(struct_id) {
        let item = tcx.hir.get(struct_id);
        let field_id = tcx.hir.as_local_node_id(field_id).unwrap();
        if let hir::map::Node::NodeItem(item) = item {
            (item, field_id)
        } else {
            bug!("Struct node should be a NodeItem {:?}", item)
        }
    } else {
        // TODO: cleanup and not sure if correct..
        let item_id = tcx.sess.cstore.maybe_get_item_body(tcx, struct_id).unwrap().value.id;
        let item = tcx.hir.get(item_id);
        let field_id = tcx.hir.as_local_node_id(field_id).unwrap();
        if let hir::map::Node::NodeItem(item) = item {
            (item, field_id)
        } else {
            bug!("Struct node should be a inlined item {:?}", item)
        }
    };

    if let hir::Item_::ItemStruct(ref variant_data, _) = item.node {
        let field = variant_data.fields().iter()
                                .find(|field| field.id == field_id)
                                .expect("Unable to find struct field by id");
        match parse(tcx.sess, &field.attrs) {
            Ok(attrs) => attrs,
            Err(mut err) => {
                err.emit();
                Vec::new()
            }
        }
    } else {
        bug!("Struct item node should be a struct {:?}", item.node)
    }
}

pub fn parse<'a>(sess: &'a Session, ast_attribs: &[syntax::ast::Attribute]) -> PResult<'a, Vec<Attribute>> {
    let mut attrs = Vec::new();

    for attr in ast_attribs {
        let items = {
            // ignore non-`#[inspirv(..)]` attributes
            if let MetaItemKind::List(ref items) = attr.value.node {
                if &*attr.value.name.as_str() == "inspirv" {
                    items
                } else { continue; }
            } else { continue; }
        };
        
        for item in items {
            match item.node {
                NestedMetaItemKind::MetaItem(ref item) => {
                    match item.node {
                        MetaItemKind::NameValue(ref value) => {
                            match &*item.name.as_str() {
                                "entry_point" => {
                                    let stage = execution_model_from_str(sess, &*extract_attr_str(value)).map_err(|err| err.set_span(value.span) )?;
                                    attrs.push(Attribute::EntryPoint {
                                        stage: stage,
                                        execution_modes: HashMap::new(),
                                    });
                                }
                                "location" => {
                                    match value.node {
                                        LitKind::Int(b, LitIntType::Unsigned(..))
                                        | LitKind::Int(b, LitIntType::Unsuffixed) => attrs.push(Attribute::Location { location: b as u64 }),
                                        _ => return Err(sess.struct_span_err(value.span, "Inspirv: Location value must be an integer")),
                                    };
                                },
                                "builtin" => {
                                    let builtin = builtin_from_str(sess, &*extract_attr_str(value)).map_err(|err| { err.set_span(value.span) } )?;
                                    attrs.push(Attribute::Builtin { builtin: builtin });
                                },

                                _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown attribute item")),
                            }
                        },
                        MetaItemKind::Word => {
                            match &*item.name.as_str() {
                                "compiler_builtin" => attrs.push(Attribute::CompilerBuiltin),
                                "interface" => attrs.push(Attribute::Interface),
                                "const_buffer" => attrs.push(Attribute::ConstBuffer),
                                _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown attribute item")),
                            }
                        },
                        MetaItemKind::List(ref items) => {
                            match &*item.name.as_str() {
                                "vector" => {
                                    let mut components = None;
                                    for item in items {
                                        match item.node {
                                            NestedMetaItemKind::MetaItem(ref item) => {
                                                match item.node {
                                                    MetaItemKind::NameValue(ref value) => {
                                                        match &*item.name.as_str() {
                                                            "components" => {
                                                                components = match value.node {
                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                    _ => return Err(sess.struct_span_err(value.span, "Inspirv: vector component value must be an integer (>2)")),
                                                                }
                                                            }
                                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown vector attribute item")),
                                                        }
                                                    }
                                                    _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown vector attribute item")),
                                                }
                                            }
                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown vector attribute item")),
                                        }
                                    }

                                    if components.is_none() {
                                        return Err(sess.struct_span_err(item.span, "Inspirv: vector misses `base` or `component` attributes"));
                                    } else {
                                        attrs.push(Attribute::Vector { 
                                            components: components.unwrap() as u64,
                                        });
                                    }
                                }

                                "matrix" => {
                                    let mut rows = None;
                                    let mut cols = None;
                                    for item in items {
                                        match item.node {
                                            NestedMetaItemKind::MetaItem(ref item) => {
                                                match item.node {
                                                    MetaItemKind::NameValue(ref value) => {
                                                        match &*item.name.as_str() {
                                                            "rows" => {
                                                                rows = match value.node {
                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                    _ => return Err(sess.struct_span_err(value.span, "Inspirv: matrix rows value must be an integer (>2)")),
                                                                }
                                                            }
                                                            "cols" => {
                                                                cols = match value.node {
                                                                    syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                    _ => return Err(sess.struct_span_err(value.span, "Inspirv: matrix cols value must be an integer (>2)")),
                                                                }
                                                            }
                                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown matrix attribute item")),
                                                        }
                                                    }
                                                    _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown matrix attribute item")),
                                                }
                                            }
                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown matrix attribute item")),
                                        }
                                    }

                                    if rows.is_none() || cols.is_none() {
                                        return Err(sess.struct_span_err(item.span, "Inspirv: matrix misses `rows` or `cols` attributes"));
                                    } else {
                                        attrs.push(Attribute::Matrix { 
                                            rows: rows.unwrap() as u64,
                                            cols: cols.unwrap() as u64,
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
                                                    MetaItemKind::NameValue(ref value) => {
                                                        match &*item.name.as_str() {
                                                            "set" => {
                                                                set = match value.node {
                                                                    syntax::ast::LitKind::Int(b, _) => Some(b),
                                                                    _ => return Err(sess.struct_span_err(value.span, "Inspirv: descriptor set value must be an integer")),
                                                                }
                                                            }
                                                            "binding" => {
                                                                binding = match value.node {
                                                                    syntax::ast::LitKind::Int(b, _) => Some(b),
                                                                    _ => return Err(sess.struct_span_err(value.span, "Inspirv: descriptor binding value value must be an integer")),
                                                                }
                                                            }
                                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown descriptor attribute item")),
                                                        }
                                                    }
                                                    _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown descriptor attribute item")),
                                                }
                                            }
                                            _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown descriptor attribute item")),
                                        }
                                    }

                                    if set.is_none() || binding.is_none() {
                                        sess.span_err(item.span, "`inspirv` descriptor misses `set` or `binding` attributes");
                                    } else {
                                        attrs.push(Attribute::Descriptor { 
                                            set: set.unwrap() as u64,
                                            binding: binding.unwrap() as u64,
                                        });
                                    }
                                }

                                // intrinsics with additional data `instrinsic(name(..))` or `instrinsic(name)`
                                "intrinsic" => {
                                    match items[0].node {
                                        NestedMetaItemKind::MetaItem(ref item) => {
                                            match item.node {
                                                MetaItemKind::List(ref items) => {
                                                    match &*item.name.as_str() {
                                                        "shuffle" => {
                                                            let mut num_components_in0 = None;
                                                            let mut num_components_in1 = None;
                                                            let mut num_components_out = None;
                                                            for item in items {
                                                                match item.node {
                                                                    NestedMetaItemKind::MetaItem(ref item) => {
                                                                        match item.node {
                                                                            MetaItemKind::NameValue(ref value) => {
                                                                                match &*item.name.as_str() {
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
                                                                            MetaItemKind::NameValue(ref value) => {
                                                                                match &*item.name.as_str() {
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
                                                        _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown intrinsic")),
                                                    } 
                                                }
                                                MetaItemKind::Word => {
                                                    let intrinsic = match &*item.name.as_str() {
                                                        "add" => Intrinsic::Add,
                                                        "sub" => Intrinsic::Sub,
                                                        "mul" => Intrinsic::Mul,
                                                        "transpose" => Intrinsic::Transpose,
                                                        "inverse" => Intrinsic::Inverse,
                                                        "outer_product" => Intrinsic::OuterProduct,
                                                        "normalize" => Intrinsic::Normalize,
                                                        "cross" => Intrinsic::Cross,
                                                        "deref" => Intrinsic::Deref,
                                                        _ => {
                                                            sess.span_err(item.span, "Unknown `inspirv` intrinsic");
                                                            continue;
                                                        }
                                                    };

                                                    attrs.push(Attribute::Intrinsic(intrinsic));
                                                }
                                                _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown intrinsic attribute item")),
                                            }
                                        }
                                        _ => return Err(sess.struct_span_err(items[0].span, "Inspirv: Unknown attribute item")),
                                    }
                                }
                                _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown attribute item")),
                            }  
                        },
                    }
                },
                _ => return Err(sess.struct_span_err(item.span, "Inspirv: Unknown attribute item")),
            }
        }
    }

    Ok(attrs)
}

fn execution_model_from_str<'a>(sess: &'a Session, name: &str) -> PResult<'a, ExecutionModel> {
    use inspirv::core::enumeration::ExecutionModel::*;
    match name {
        "vertex" => Ok(ExecutionModelVertex),
        "tessellation_control" => Ok(ExecutionModelTessellationControl),
        "tessellation_eval" => Ok(ExecutionModelTessellationEvaluation),
        "geometry" => Ok(ExecutionModelGeometry),
        "fragment" => Ok(ExecutionModelFragment),
        "compute" => Ok(ExecutionModelGLCompute),
        "kernel" => Ok(ExecutionModelKernel),
        _ => Err(sess.struct_err("Inspirv: Unknown execution model")),
    }
}

fn builtin_from_str<'a>(sess: &'a Session, name: &str) -> PResult<'a, BuiltIn> {
    use inspirv::core::enumeration::BuiltIn::*;
    match name {
        // Should be all possible builtIn's for shaders 
        "Position" => Ok(BuiltInPosition),
        "PointSize" => Ok(BuiltInPointSize),
        "ClipDistance" => Ok(BuiltInClipDistance),
        "CullDistance" => Ok(BuiltInCullDistance),
        "VertexId" => Ok(BuiltInVertexId),
        "InstanceId" => Ok(BuiltInInstanceId),
        "PrimitiveId" => Ok(BuiltInPrimitiveId),
        "Layer" => Ok(BuiltInLayer),
        "InvocationId" => Ok(BuiltInInvocationId),
        "ViewportIndex" => Ok(BuiltInViewportIndex),
        "TessLevelOuter" => Ok(BuiltInTessLevelOuter),
        "TessLevelInner" => Ok(BuiltInTessLevelInner),
        "TessCoord" => Ok(BuiltInTessCoord),
        "PatchVertices" => Ok(BuiltInPatchVertices),
        "FragCoord" => Ok(BuiltInFragCoord),
        "PointCoord" => Ok(BuiltInPointCoord),
        "FrontFacing" => Ok(BuiltInFrontFacing),
        "SampleId" => Ok(BuiltInSampleId),
        "SamplePosition" => Ok(BuiltInSamplePosition),
        "SampleMask" => Ok(BuiltInSampleMask),
        "FragDepth" => Ok(BuiltInFragDepth),
        "HelperInvocation" => Ok(BuiltInHelperInvocation),
        "NumWorkgroups" => Ok(BuiltInNumWorkgroups),
        "WorkgroupSize" => Ok(BuiltInWorkgroupSize),
        "WorkgroupId" => Ok(BuiltInWorkgroupId),
        "LocalInvocationId" => Ok(BuiltInLocalInvocationId),
        "GlobalInvocationId" => Ok(BuiltInGlobalInvocationId),
        "LocalInvocationIndex" => Ok(BuiltInLocalInvocationIndex),
        "VertexIndex" => Ok(BuiltInVertexIndex),
        "InstanceIndex" => Ok(BuiltInInstanceIndex),
        _ => Err(sess.struct_err("Inspirv: Unknown builtin")),
    }
}

fn extract_attr_str(lit: &syntax::ast::Lit) -> InternedString {
    match lit.node {
        syntax::ast::LitKind::Str(ref s, _) => s.as_str(),
        _ => panic!("attribute values need to be strings"),
    }
}
