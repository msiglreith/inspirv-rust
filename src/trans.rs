
use rustc_mir as mir;
use rustc::mir::transform::MirSource;
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal::*;
use rustc_const_math::{ConstInt, ConstFloat};
use rustc::ty::{self, TyCtxt, Ty};
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::util::common::time;
use rustc_borrowck as borrowck;
use rustc_data_structures::indexed_vec::{Idx, IndexVec};
use syntax;
use syntax::ast::{LitKind, LitIntType, NodeId, IntTy, UintTy, FloatTy, MetaItemKind, NestedMetaItemKind};
use std::collections::HashMap;
use std::fs::File;
use inspirv;
use inspirv::instruction;
use inspirv::types::*;
use inspirv::core::instruction::*;
use inspirv::core::enumeration::*;
use inspirv::instruction::BranchInstruction;
use inspirv_builder::function::{Argument, LocalVar, Block};
use inspirv_builder::module::{self, Type, ModuleBuilder, ConstValue, ConstValueFloat};

// const SOURCE_INSPIRV_RUST: u32 = 0xCC; // TODO: might get an official number in the future?
const VERSION_INSPIRV_RUST: u32 = 0x00010000; // |major(1 byte)|minor(1 byte)|patch(2 byte)|

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Intrinsic {
    Swizzle {
        components_out: u32,
        components_in: u32
    },
    Shuffle {
        components_out: u32,
        components_in0: u32,
        components_in1: u32
    },
    VectorNew { components: u32 },
}

#[derive(Clone, Debug)]
enum InspirvAttribute {
    Interface,
    ConstBuffer,
    Location {
        location: u64,
    },
    Vector {
        base: Box<Type>,
        components: u64,
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
}

pub fn translate_to_spirv<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>,
                                    mut mir_map: &mut MirMap<'tcx>,
                                    analysis: &ty::CrateAnalysis) {
    let time_passes = tcx.sess.time_passes();

    // Run the passes that transform the MIR into a more suitable for translation
    time(time_passes, "Prepare MIR codegen passes", || {
        let mut passes = ::rustc::mir::transform::Passes::new();
        passes.push_hook(box mir::transform::dump_mir::DumpMir);
        passes.push_pass(box mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box mir::transform::simplify_cfg::SimplifyCfg::new("no-landing-pads"));

        passes.push_pass(box mir::transform::erase_regions::EraseRegions);

        passes.push_pass(box mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box borrowck::ElaborateDrops);
        passes.push_pass(box mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box mir::transform::simplify_cfg::SimplifyCfg::new("elaborate-drops"));

        passes.push_pass(box mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box mir::transform::dump_mir::Marker("PreTrans"));

        passes.run_passes(*tcx, &mut mir_map);
    });

    time(time_passes,
         "translation",
         move || trans_crate(tcx, mir_map, analysis));
}

fn trans_crate<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>,
                         mir_map: &MirMap<'tcx>,
                         _analysis: &ty::CrateAnalysis) {
    let mut builder = ModuleBuilder::new();
    builder.with_source(SourceLanguage::SourceLanguageUnknown, VERSION_INSPIRV_RUST);

    let mut v = InspirvModuleCtxt {
        tcx: tcx,
        mir_map: mir_map,
        builder: builder,

        arg_ids: IndexVec::new(),
        var_ids: IndexVec::new(),
        temp_ids: IndexVec::new(),
        return_ids: None,
    };

    v.trans();
}

type TypedId = (Id, Type);

#[derive(Clone, Debug)]
enum SpirvOperand {
    Consume(SpirvLvalue),
    Constant(Id, Type),
    FnCall(DefId),
    None, // TODO: temp
}

impl SpirvOperand {
    fn is_constant(&self) -> bool {
        match *self {
            SpirvOperand::Constant(..) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
enum SpirvLvalue {
    Variable(Id, Type, StorageClass),
    SignatureStruct(Vec<(Id, Type)>, StorageClass), // struct objects passed to functions, e.g. interfaces, constant buffer, ..
    AccessChain(Id, StorageClass, Vec<Id>, Type),
    Return(Id, Type),
    Ignore, // Ignore this lvalue, e.g. return = ()
}

#[derive(Clone)]
enum FuncArg {
    Argument(Argument),
    Interface(Vec<(Id, Type)>),
    ConstBuffer(Vec<(Id, Type)>),
}

#[derive(Clone)]
enum FuncReturn {
    Return(LocalVar),
    Interface(Vec<(Id, Type)>),
}

struct InspirvModuleCtxt<'v, 'tcx: 'v> {
    tcx: &'v TyCtxt<'v, 'tcx, 'tcx>,
    mir_map: &'v MirMap<'tcx>,
    builder: ModuleBuilder,

    arg_ids: IndexVec<Arg, Option<FuncArg>>,
    var_ids: IndexVec<Var, LocalVar>,
    temp_ids: IndexVec<Temp, LocalVar>,
    return_ids: Option<FuncReturn>,
}

struct InspirvBlock<'a, 'b, 'v: 'a, 'tcx: 'v> {
    ctxt: &'a mut InspirvModuleCtxt<'v, 'tcx>,
    block: &'b mut Block,
    labels: &'b IndexVec<BasicBlock, Id>,
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

impl<'v, 'tcx> InspirvModuleCtxt<'v, 'tcx> {
    fn trans(&mut self) {
        let def_ids = self.mir_map.map.keys();
        for def_id in def_ids {
            let mir = self.mir_map.map.get(&def_id).unwrap();
            let id = self.tcx.map.as_local_node_id(def_id).unwrap();
            let src = MirSource::from_node(*self.tcx, id);

            match src {
                MirSource::Const(id) => self.trans_const(id, mir),
                MirSource::Fn(id) => self.trans_fn(id, mir),
                MirSource::Static(id, mutability) => self.trans_static(id, mutability, mir),
                MirSource::Promoted(id, promoted) => {
                    println!("{:?}", (id, promoted, mir));
                }
            }
        }

        let out_file = File::create("example.spv").unwrap();
        self.builder.build().ok().unwrap().export_binary(out_file);

        let file = File::open("example.spv").unwrap();
        let mut reader = inspirv::read_binary::ReaderBinary::new(file).unwrap();

        while let Some(instr) = reader.read_instruction().unwrap() {
            println!("{:?}", instr);
        }
    }

    fn parse_inspirv_attributes(&self, ast_attribs: &[syntax::ast::Attribute]) -> Vec<InspirvAttribute> {
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
                                                    attrs.push(InspirvAttribute::EntryPoint {
                                                        stage: stage,
                                                        execution_modes: HashMap::new(),
                                                    });
                                                } else {
                                                    self.tcx.sess.span_err(item.span, "Unknown `inspirv` entry_point execution model");
                                                }
                                            },
                                            "location" => {
                                                match value.node {
                                                    LitKind::Int(b, LitIntType::Unsigned(..))
                                                    | LitKind::Int(b, LitIntType::Unsuffixed) => attrs.push(InspirvAttribute::Location { location: b }),
                                                    _ => panic!("attribute value need to be valid unsigned interger"),
                                                };
                                            },
                                            "builtin" => {
                                                let builtin = builtin_from_str(&*extract_attr_str(value));
                                                if let Some(builtin) = builtin {
                                                    attrs.push(InspirvAttribute::Builtin { builtin: builtin });
                                                } else {
                                                    self.tcx.sess.span_err(item.span, "Unknown `inspirv` builtin variable");
                                                }
                                            },

                                            _ => {
                                                self.tcx.sess.span_err(item.span, "Unknown `inspirv` attribute name value item")
                                            }
                                        }
                                    },
                                    MetaItemKind::Word(ref name) => {
                                        match &**name {
                                            "compiler_builtin" => attrs.push(InspirvAttribute::CompilerBuiltin),
                                            "interface" => attrs.push(InspirvAttribute::Interface),
                                            "const_buffer" => attrs.push(InspirvAttribute::ConstBuffer),
                                            _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv`attribute word item"),
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
                                                                        "components" => { // TODO: low: check > 1
                                                                            components = match value.node {
                                                                                syntax::ast::LitKind::Int(b, _) if b >= 2 => Some(b),
                                                                                _ => panic!("attribute value needs to be interger (>2)"),
                                                                            }
                                                                        },
                                                                        "base" => {
                                                                            base = match &*extract_attr_str(value) {
                                                                                "bool" => Some(Type::Bool),
                                                                                "f32" => Some(Type::Float(32)),
                                                                                "f64" => Some(Type::Float(64)),

                                                                                _ => {
                                                                                    self.tcx.sess.span_err(item.span, "Unsupported `inspirv` vector base type");
                                                                                    None
                                                                                }
                                                                            }
                                                                        },

                                                                        _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                                    }
                                                                }
                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                            }
                                                        }
                                                        _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` vector attribute item"),
                                                    }
                                                }

                                                if base.is_none() || components.is_none() {
                                                    self.tcx.sess.span_err(item.span,
                                                                           "`inspirv` vector \
                                                                            misses `base` or \
                                                                            `component` \
                                                                            attributes");
                                                } else {
                                                    attrs.push(InspirvAttribute::Vector { 
                                                        base: Box::new(base.unwrap()),
                                                        components: components.unwrap()
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

                                                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                                            }
                                                                                        }
                                                                                        _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                                    }
                                                                                }
                                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` shuffle intrinsic attribute item"),
                                                                            }
                                                                        }
                                                                        if num_components_in0.is_none() ||
                                                                           num_components_in1.is_none() ||
                                                                           num_components_out.is_none() {
                                                                            self.tcx.sess.span_err(item.span, "`inspirv` shuffle misses `num_in0`, `num_in1` or `num_out` attributes");
                                                                        } else {
                                                                            let intrinsic = Intrinsic::Shuffle {
                                                                                components_out: num_components_out.unwrap(),
                                                                                components_in0: num_components_in0.unwrap(),
                                                                                components_in1: num_components_in1.unwrap(),
                                                                            };
                                                                            attrs.push(InspirvAttribute::Intrinsic(intrinsic));
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

                                                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                                            }
                                                                                        }
                                                                                        _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                                    }
                                                                                }
                                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` swizzle intrinsic attribute item"),
                                                                            }
                                                                        }
                                                                        if num_components_in.is_none() ||
                                                                           num_components_out.is_none() {
                                                                            self.tcx.sess.span_err(item.span, "`inspirv` swizzle misses `num_in` or `num_out` attributes");
                                                                        } else {
                                                                            let intrinsic = Intrinsic::Swizzle {
                                                                                components_out: num_components_out.unwrap(),
                                                                                components_in: num_components_in.unwrap(),
                                                                            };
                                                                            attrs.push(InspirvAttribute::Intrinsic(intrinsic));
                                                                        }
                                                                    }
                                                                    "vector_new" => {
                                                                        let mut components = None;
                                                                        for item in items {
                                                                            match item.node {
                                                                                NestedMetaItemKind::Literal(ref literal) => {
                                                                                    match literal.node {
                                                                                        syntax::ast::LitKind::Int(b, _) if b >= 2 => components = Some(b as u32),
                                                                                        _ => panic!("attribute value needs to be interger (>2)"),
                                                                                    }
                                                                                }
                                                                                _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` vector_new intrinsic attribute item"),
                                                                            }
                                                                        }
                                                                        if let Some(components) = components {
                                                                            let intrinsic = Intrinsic::VectorNew {
                                                                                components: components,
                                                                            };
                                                                            attrs.push(InspirvAttribute::Intrinsic(intrinsic));
                                                                        } else {
                                                                            self.tcx.sess.span_err(item.span, "`inspirv` vector_new misses components attributes");
                                                                        }
                                                                    }
                                                                    _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` intrinsic"),
                                                                } 
                                                            }
                                                            MetaItemKind::Word(ref name) => {
                                                                match &**name {
                                                                    _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` intrinsic"),
                                                                }
                                                            }
                                                            _ => self.tcx.sess.span_err(item.span, "Unknown `inspirv` intrinsic attribute item"),
                                                        }
                                                    }
                                                    _ => self.tcx.sess.span_err(items[0].span, "Unknown `inspirv` intrinsic attribute item"),
                                                }
                                            }
                                            _ => self.tcx.sess.span_err(item.span,
                                                                       "Unknown `inspirv` \
                                                                        attribute list item"),
                                        }  
                                    },
                                }
                            },
                            _ => {
                                self.tcx.sess.span_err(item.span,
                                                       "Unknown `inspirv` attribute nested item.")
                            }
                        }
                    }
                }

                _ => (), // ignore non-`#[inspirv(..)]` attributes
            }
        }

        attrs
    }

    // TODO: remove ugly clones..
    fn resolve_lvalue(&mut self, lvalue: &Lvalue<'tcx>) -> Option<SpirvLvalue> {
        use rustc::mir::repr::Lvalue::*;
        use inspirv::core::enumeration::StorageClass::*;
        match *lvalue {
            Arg(id) => {
                if let Some(arg) = self.arg_ids[id].clone() {
                    match arg {
                        FuncArg::Argument(arg) => Some(SpirvLvalue::Variable(arg.id, arg.ty, StorageClassFunction)),
                        FuncArg::Interface(interfaces) => Some(SpirvLvalue::SignatureStruct(interfaces, StorageClassInput)),
                        FuncArg::ConstBuffer(_consts) => None, // TODO: High
                    }
                } else {
                    Some(SpirvLvalue::Ignore) // unnamed argument `_`
                }
            }
            Var(id) => {
                let var = self.var_ids[id].clone();
                Some(SpirvLvalue::Variable(var.id, var.ty, StorageClassFunction))
            }
            Temp(id) => {
                let var = self.temp_ids[id].clone();
                Some(SpirvLvalue::Variable(var.id, var.ty, StorageClassFunction))
            }
            ReturnPointer => {
                match self.return_ids {
                    Some(FuncReturn::Return(ref var)) => Some(SpirvLvalue::Return(var.id, var.ty.clone())),
                    Some(FuncReturn::Interface(ref interfaces)) => Some(SpirvLvalue::SignatureStruct(interfaces.clone(), StorageClassOutput)),
                    None => Some(SpirvLvalue::Ignore),
                }
            }
            Static(_def_id) => {
                println!("inspirv: unsupported lvalue {:?}", lvalue);
                None
            }
            Projection(ref proj) => {
                if let Some(base) = self.resolve_lvalue(&proj.base) {
                    match (&proj.elem, &base) {
                        (&ProjectionElem::Field(field, _), &SpirvLvalue::SignatureStruct(ref interfaces, storage_class)) => {
                            let var = interfaces[field.index()].clone();
                            Some(SpirvLvalue::Variable(var.0, var.1, storage_class))
                        }
                        (&ProjectionElem::Field(field, ty), &SpirvLvalue::Variable(id, _, storage_class)) => {
                            let field_id = self.builder.define_constant(module::Constant::Scalar(ConstValue::U32(field.index() as u32)));
                            Some(SpirvLvalue::AccessChain(id, storage_class, vec![field_id], self.rust_ty_to_inspirv(ty)))
                        }
                        (&ProjectionElem::Field(field, ty), &SpirvLvalue::AccessChain(id, storage_class, ref chain, _)) => {
                            let field_id = self.builder.define_constant(module::Constant::Scalar(ConstValue::U32(field.index() as u32)));
                            let mut chain = chain.clone();
                            chain.push(field_id);
                            Some(SpirvLvalue::AccessChain(id, storage_class, chain, self.rust_ty_to_inspirv(ty)))
                        }
                        _ => {
                            println!("inspirv: unsupported lvalue {:?}", (proj, &base));
                            None
                        }
                    }
                } else {
                    println!("inspirv: unsupported lvalue projection base {:?}", lvalue);
                    None
                }
            },
        }
    }

    fn transform_lvalue(&mut self, block: &mut Block, lvalue: SpirvLvalue) -> SpirvLvalue {
        match lvalue {
            SpirvLvalue::AccessChain(root_id, storage_class, ref chain, ref ty) => {
                let chain_id = self.builder.alloc_id();
                let ty_id = self.builder.define_type(&Type::Pointer(Box::new(ty.clone()), storage_class));
                let op_access_chain = OpAccessChain(ty_id, chain_id, root_id, chain.clone());
                block.emit_instruction(op_access_chain);
                SpirvLvalue::Variable(chain_id, ty.clone(), storage_class)
            },
            _ => lvalue
        }
    }

    fn extract_u32_from_operand(&mut self, operand: &Operand<'tcx>) -> u32 {
        match *operand {
            Operand::Constant(ref c) => {
                match c.literal {
                    Literal::Value { value: Integral(ConstInt::U32(v)) } => v,
                    _ => bug!("Expected u32 constant `{:?}", operand)
                }
            }
            _ => bug!("Expected constant operand `{:?}`", operand)
        }
    }

    fn trans_static(&mut self, id: NodeId, mutability: hir::Mutability, mir: &'v Mir<'tcx>) {
        println!("{:?}", (id, mutability, mir));
    }

    fn trans_const(&mut self, id: NodeId, mir: &'v Mir<'tcx>) {
        println!("{:?} {:?}", id, mir);
    }

    fn trans_fn(&mut self, id: NodeId, mir: &'v Mir<'tcx>) {
        self.arg_ids = IndexVec::new();
        let mut fn_module = {
            let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(id));

            // We don't translate builtin functions, these will be handled internally
            if attrs.iter().any(|attr| match *attr { InspirvAttribute::CompilerBuiltin | InspirvAttribute::Intrinsic(..) => true, _ => false }) {
                return;
            }

            let fn_name = &*self.tcx.map.name(id).as_str();

            // check if we have an entry point
            let entry_point = attrs.iter().find(|attr| match **attr {
                InspirvAttribute::EntryPoint { .. } => true,
                _ => false,
            });

            let mut interface_ids = Vec::new(); // entry points
            let mut params = Vec::new(); // `normal` function

            // Extract all arguments and store their ids in a list for faster access later
            // Arguments as Input interface if the structs have to corresponding annotations
            for arg in mir.arg_decls.iter() {
                let name = &*arg.debug_name.as_str();
                if name.is_empty() {
                    self.arg_ids.push(None);
                } else if let Some(ty_id) = arg.ty.ty_to_def_id() {
                    // TODO: low-mid: unsafe! We would like to find the attributes of the current type
                    // Dont know how to correctly retrieve this information for non-local crates!
                    let node_id = self.tcx.map.as_local_node_id(ty_id).unwrap();
                    let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));

                    let interface = attrs.iter().any(|attr| match *attr {
                            InspirvAttribute::Interface => true,
                            _ => false,
                        });
                    let const_buffer = attrs.iter().any(|attr| match *attr {
                            InspirvAttribute::ConstBuffer => true,
                            _ => false,
                        });

                    if interface {
                        if let ty::TyAdt(adt, subs) = arg.ty.sty {
                            let interfaces = adt.struct_variant().fields.iter().map(|field| {
                                let ty = self.rust_ty_to_inspirv(field.ty(*self.tcx, subs));
                                let name = format!("{}::{}", self.tcx.map.name(node_id), field.name.as_str());
                                let id = self.builder.define_variable(name.as_str(), ty.clone(),
                                                             StorageClass::StorageClassInput);

                                // HELP! A nicer way to get the attributes?
                                // Get struct field attributes
                                let node = self.tcx.map.get(node_id);
                                let field_id = self.tcx.map.as_local_node_id(field.did).unwrap();
                                let field_attrs = {
                                    if let hir::map::Node::NodeItem(item) = node {
                                        if let hir::Item_::ItemStruct(ref variant_data, _) = item.node {
                                            let field = variant_data.fields().iter()
                                                                    .find(|field| field.id == field_id)
                                                                    .expect("Unable to find struct field by id");
                                            self.parse_inspirv_attributes(&*field.attrs)
                                        } else {
                                            bug!("Struct item node should be a struct {:?}", item.node)
                                        }
                                    } else {
                                        bug!("Struct node should be a NodeItem {:?}", node)
                                    }
                                };

                                for attr in field_attrs {
                                    match attr {
                                        InspirvAttribute::Location { location } => {
                                            self.builder.add_decoration(id, Decoration::DecorationLocation(LiteralInteger(location as u32)));
                                        }
                                        // Rust doesn't allow attributes associated with `type foo = bar` /:
                                        InspirvAttribute::Builtin { builtin } => {
                                            // TODO: check if our decorations follow Vulkan specs e.g. Position only for float4
                                            self.builder.add_decoration(id, Decoration::DecorationBuiltIn(builtin));
                                        }
                                        _ => ()
                                    }
                                }

                                interface_ids.push(id);
                                (id, ty)
                            }).collect::<Vec<_>>();

                            self.arg_ids.push(Some(FuncArg::Interface(interfaces)));
                        } else {
                            bug!("Input argument type requires to be struct type ({:?})", arg.ty)
                        }
                    } else if const_buffer {
                        if let ty::TyAdt(_adt, _subs) = arg.ty.sty {

                        } else {
                            bug!("Const buffer argument type requires to be struct type ({:?})", arg.ty)
                        }
                    } else if entry_point.is_some() {
                        // Entrypoint functions don't have actual input/output parameters
                        // We use them for the shader interface and const buffers
                        bug!("Input argument type requires interface or const_buffer attribute({:?})", arg.ty)
                    } else {
                        let id = self.builder.alloc_id();
                        let arg = Argument {
                            id: id,
                            ty: self.rust_ty_to_inspirv(arg.ty),
                        };
                        params.push(arg.clone());
                        self.builder.name_id(id, &*name); // TODO: hide this behind a function module interface
                        self.arg_ids.push(Some(FuncArg::Argument(arg)));
                    }
                } else if entry_point.is_some() {
                    bug!("Argument type not defined in local crate({:?})", arg.ty)
                } else {
                    //
                    let id = self.builder.alloc_id();
                    let arg = Argument {
                        id: id,
                        ty: self.rust_ty_to_inspirv(arg.ty),
                    };
                    params.push(arg.clone());
                    self.builder.name_id(id, &*name); // TODO: hide this behind a function module interface
                    self.arg_ids.push(Some(FuncArg::Argument(arg)));
                }
            }

            // Entry Point Handling
            // These functions don't have actual input/output parameters
            // We use them for the shader interface and uniforms
            if let Some(&InspirvAttribute::EntryPoint{ stage, ref execution_modes }) = entry_point {
                // TODO: high: input parameters are passed by value
                // This required handling of the different attributes attached to the parameter types
                // Return type as Output interface
                match mir.return_ty.sty {
                    ty::TyAdt(adt, subs) => {
                        if let Some(ty_id) = mir.return_ty.ty_to_def_id() {
                            let node_id = self.tcx.map.as_local_node_id(ty_id).unwrap();
                            let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));

                            let interface = attrs.iter().any(|attr| match *attr {
                                InspirvAttribute::Interface => true,
                                _ => false,
                            });

                            if interface {
                                let interfaces = adt.struct_variant().fields.iter().map(|field| {
                                    let ty = self.rust_ty_to_inspirv(field.ty(*self.tcx, subs));
                                    let name = format!("{}::{}", self.tcx.map.name(node_id), field.name.as_str());
                                    let id = self.builder.define_variable(name.as_str(), ty.clone(),
                                                                 StorageClass::StorageClassOutput);

                                    // HELP! A nicer way to get the attributes?
                                    // Get struct field attributes
                                    let node = self.tcx.map.get(node_id);
                                    let field_id = self.tcx.map.as_local_node_id(field.did).unwrap();
                                    let field_attrs = {
                                        if let hir::map::Node::NodeItem(item) = node {
                                            if let hir::Item_::ItemStruct(ref variant_data, _) = item.node {
                                                let field = variant_data.fields().iter()
                                                                        .find(|field| field.id == field_id)
                                                                        .expect("Unable to find struct field by id");
                                                self.parse_inspirv_attributes(&*field.attrs)
                                            } else {
                                                bug!("Struct item node should be a struct {:?}", item.node)
                                            }
                                        } else {
                                            bug!("Struct node should be a NodeItem {:?}", node)
                                        }
                                    };

                                    for attr in field_attrs {
                                        match attr {
                                            InspirvAttribute::Location { location } => {
                                                self.builder.add_decoration(id, Decoration::DecorationLocation(LiteralInteger(location as u32)));
                                            }
                                            // Rust doesn't allow attributes associated with `type foo = bar` /:
                                            InspirvAttribute::Builtin { builtin } => {
                                                // TODO: check if our decorations follow Vulkan specs e.g. Position only for float4
                                                self.builder.add_decoration(id, Decoration::DecorationBuiltIn(builtin));
                                            }
                                            _ => ()
                                        }
                                    }

                                    interface_ids.push(id);
                                    (id, ty)
                                }).collect::<Vec<_>>();
                                self.return_ids = Some(FuncReturn::Interface(interfaces));
                            } else {
                                bug!("Output argument type requires interface attribute({:?})", mir.return_ty)
                            }
                        } else {
                            bug!("Output argument type not defined in local crate({:?})", mir.return_ty)
                        }
                    },

                    ty::TyTuple(&[]) => self.return_ids = None, // MIR doesn't use void(!) instead the () type for some reason \o/

                    _ => bug!("Output argument type requires to be a struct type or empty ({:?})", mir.return_ty)
                }

                //
                let mut execution_modes = execution_modes.clone();
                if stage == ExecutionModel::ExecutionModelFragment {
                    execution_modes.insert(ExecutionModeKind::ExecutionModeOriginUpperLeft, ExecutionMode::ExecutionModeOriginUpperLeft);
                }

                // Define entry point in SPIR-V
                let mut func = self.builder
                    .define_entry_point(fn_name, stage, execution_modes, interface_ids)
                    .ok()
                    .unwrap();

                func.ret_ty = Type::Void;
                func
            } else {
                let mut func = self.builder.define_function_named(fn_name);

                func.params = params;

                let return_ty = self.rust_ty_to_inspirv(mir.return_ty);
                self.return_ids = if let Type::Void = return_ty {
                    None
                } else {
                    let id = self.builder.alloc_id();
                    let local_var = LocalVar {
                        id: id,
                        ty: return_ty.clone(),
                    };
                    func.variables.push(local_var.clone());
                    Some(FuncReturn::Return(local_var))
                };

                func.ret_ty = return_ty;
                func
            }
        };

        println!("{:?}", (id, self.tcx.map.name(id).as_str(), mir));

        // local variables and temporaries
        self.var_ids = {
            let mut ids: IndexVec<Var, LocalVar> = IndexVec::new();
            for var in mir.var_decls.iter() {
                let id = self.builder.alloc_id();
                let local_var = LocalVar {
                    id: id,
                    ty: self.rust_ty_to_inspirv(var.ty),
                };
                fn_module.variables.push(local_var.clone());
                ids.push(local_var);
                self.builder.name_id(id, &*var.name.as_str()); // TODO: hide this behind a function module interface
            }
            ids
        };

        self.temp_ids = {
            let mut ids: IndexVec<Temp, LocalVar> = IndexVec::new();
            for var in mir.temp_decls.iter() {
                let id = self.builder.alloc_id();
                let local_var = LocalVar {
                    id: id,
                    ty: self.rust_ty_to_inspirv(var.ty),
                };
                fn_module.variables.push(local_var.clone());
                ids.push(local_var);
            }
            ids
        };

        // Translate blocks
        let mut block_labels: IndexVec<BasicBlock, Id> = IndexVec::new();
        for _ in mir.basic_blocks().iter() {
            let block = fn_module.add_block(self.builder.alloc_id());
            block_labels.push(block.label);
        }

        for (i, bb) in mir.basic_blocks().iter().enumerate() {
            println!("bb{}: {:#?}", i, bb);

            let mut block_ctxt = InspirvBlock {
                ctxt: self,
                block: &mut fn_module.blocks[i],
                labels: &block_labels,
            };

            for stmt in &bb.statements {
                block_ctxt.trans_stmnt(stmt);
            }

            block_ctxt.trans_terminator(bb.terminator());
        }

        // Push function and clear variable stack
        self.builder.push_function(fn_module);
        self.arg_ids = IndexVec::new();
        self.var_ids = IndexVec::new();
        self.temp_ids = IndexVec::new();
    }

    // TODO: low: We could cache some aggregated types for faster compilation
    fn rust_ty_to_inspirv(&self, t: Ty<'tcx>) -> Type {
        match t.sty {
            ty::TyBool => Type::Bool,
            ty::TyInt(IntTy::I8)      => Type::Int(8, true),
            ty::TyInt(IntTy::I16)     => Type::Int(16, true),
            ty::TyInt(IntTy::Is) |
            ty::TyInt(IntTy::I32)     => Type::Int(32, true), // isize
            ty::TyInt(IntTy::I64)     => Type::Int(64, true),
            ty::TyChar |
            ty::TyUint(UintTy::U8)    => Type::Int(8, false),
            ty::TyUint(UintTy::U16)   => Type::Int(16, false),
            ty::TyUint(UintTy::Us) |
            ty::TyUint(UintTy::U32)   => Type::Int(32, false), // usize
            ty::TyUint(UintTy::U64)   => Type::Int(64, false),
            ty::TyFloat(FloatTy::F32) => Type::Float(32),
            ty::TyFloat(FloatTy::F64) => Type::Float(64),
            ty::TyArray(_ty, _len)    => unimplemented!(),
            
            // TyNever:
            //  Some weird case, appearing sometimes in the code for whatever reason
            //  Often as unused temporary variables, which are never really used
            // TyTuple(&[]):
            //  Rust seems to emit () instead of void for function return types
            ty::TyNever | ty::TyTuple(&[]) => Type::Void,
            ty::TyTuple(tys)               => Type::Struct(tys.iter().map(|ty| self.rust_ty_to_inspirv(ty)).collect()),

            //
            ty::TyAdt(adt, subs) if adt.is_struct() => {
                // TODO: low-mid: unsafe! We would like to find the attributes of the current type, to look for representations as vector/matrix
                // Dont know how to correctly retrieve this information for non-local crates!
                let node_id = self.tcx.map.as_local_node_id(adt.did).unwrap();
                let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));
                let internal_type = attrs.iter().find(|attr| match **attr {
                    InspirvAttribute::Vector { .. } => true,
                    _ => false,
                });
                if let Some(internal_type) = internal_type {
                    match *internal_type {
                        InspirvAttribute::Vector { ref base, components } => Type::Vector(base.clone(), components as u32),
                        _ => bug!("Unhandled internal type ({:?})", *internal_type),
                    }
                } else {
                    // an actual struct!
                    // TODO: handle names
                    Type::Struct(adt.struct_variant().fields.iter().map(|field| self.rust_ty_to_inspirv(field.ty(*self.tcx, subs))).collect())
                }    
            },

            ty::TyRawPtr(..) => { println!("{:?}", t.sty); unimplemented!() },

            _ => { println!("{:?}", t.sty); unimplemented!() },
        }
    }
}

impl<'a, 'b, 'v: 'a, 'tcx: 'v> InspirvBlock<'a, 'b, 'v, 'tcx> {
    fn trans_stmnt(&mut self, stmt: &Statement<'tcx>) {
        match stmt.kind {
            StatementKind::Assign(ref lvalue, ref rvalue) => {
                println!("{:?}", (lvalue, rvalue));
                if let Some(lvalue) = self.ctxt.resolve_lvalue(lvalue) {
                    let lvalue = self.ctxt.transform_lvalue(self.block, lvalue);
                
                    match lvalue {
                        SpirvLvalue::Variable(lvalue_id, lvalue_ty, _) | SpirvLvalue::Return(lvalue_id, lvalue_ty) => {
                            use rustc::mir::repr::Rvalue::*;
                            match *rvalue {
                                Use(ref operand) => {
                                    let op = self.trans_operand(operand);
                                    match op {
                                        SpirvOperand::Constant(op_id, _) => {
                                            self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                        }
                                        SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                            let op_id = self.ctxt.builder.alloc_id();
                                            self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                            self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                        }
                                        SpirvOperand::Consume(SpirvLvalue::SignatureStruct(ref interfaces, _)) => {
                                            let ids = interfaces.iter().map(|interface| {
                                                let id = self.ctxt.builder.alloc_id();
                                                self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&interface.1), id, interface.0, None));
                                                id
                                            }).collect::<Vec<_>>();
                                            let composite_id = self.ctxt.builder.alloc_id();
                                            self.block.emit_instruction(OpCompositeConstruct(self.ctxt.builder.define_type(&lvalue_ty), composite_id, ids));
                                            self.block.emit_instruction(OpStore(lvalue_id, composite_id, None));
                                        }
                                        _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                           "inspirv: Unsupported rvalue!"),
                                    }
                                }

                                /// [x; 32]
                                Repeat(ref _operand, ref _times) => {}

                                Ref(_, _, _) => {
                                    self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                           "inspirv: Unsupported rvalue reference!")
                                }

                                /// length of a [X] or [X;n] value
                                Len(_ /* ref val */) => {}

                                Cast(ref kind, ref operand, ty) => {
                                    if *kind != CastKind::Misc {
                                        self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported cast kind!")
                                    } else {
                                        let op = self.trans_operand(operand);
                                        let cast_ty = self.ctxt.rust_ty_to_inspirv(ty);
                                        match op {
                                            SpirvOperand::Constant(_op_id, _op_ty) => {
                                                // Why!? ):
                                                self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported const cast rvalue (soon)!")
                                                // self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                            }
                                            SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                                let op_id = self.ctxt.builder.alloc_id();
                                                self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                                // TODO: add cast conversions
                                                match (cast_ty, op_ty) {
                                                    _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported cast conversion!"),
                                                }

                                                self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                            }
                                            _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                               "inspirv: Unsupported cast rvalue!"),
                                        }
                                    }
                                }

                                BinaryOp(ref op, ref left, ref right) |
                                CheckedBinaryOp(ref op, ref left, ref right) => {
                                    let left = self.trans_operand(left);
                                    let right = self.trans_operand(right);
                                    println!("binop: {:?}", op);

                                    match (left, right) {
                                        (SpirvOperand::Consume(SpirvLvalue::Variable(left_id, left_ty, _)),
                                         SpirvOperand::Consume(SpirvLvalue::Variable(right_id, right_ty, _))) => {
                                            self.emit_binop(*op, (lvalue_id, lvalue_ty), (left_id, left_ty), (right_id, right_ty));
                                        }

                                        // TODO:
                                        _ => (),
                                    }
                                }

                                UnaryOp(ref op, ref operand) => {
                                    let _operand = self.trans_operand(operand);
                                    println!("unop: {:?}", op);
                                    // TODO
                                }

                                Aggregate(ref _kind, ref _operands) => {}

                                Box(..) => {
                                    self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid box r-value")
                                }
                                InlineAsm { .. } => {
                                    self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid inline asm")
                                }
                            }
                        }

                        SpirvLvalue::SignatureStruct(ref interfaces, _) => {
                            use rustc::mir::repr::Rvalue::*;
                            match *rvalue {
                                Use(ref _operand) => {
                                    // TODO:
                                    self.ctxt.tcx.sess.span_warn(stmt.source_info.span,
                                                "inspirv: Unhandled use-assignment for interfaces (soon)!")
                                }

                                Aggregate(ref _kind, ref operands) => {
                                    for (operand, interface) in operands.iter().zip(interfaces.iter()) {
                                        let op = self.trans_operand(operand);
                                        match op {
                                            SpirvOperand::Constant(op_id, _) => {
                                                self.block.emit_instruction(OpStore(interface.0, op_id, None));
                                            }
                                            SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                                let op_id = self.ctxt.builder.alloc_id();
                                                self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                                self.block.emit_instruction(OpStore(interface.0, op_id, None));
                                            }
                                            _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                               "inspirv: Unsupported aggregate operand!"),
                                        }
                                    }
                                }

                                _ => bug!("Unexpected rvalue for an interface ({:?})", rvalue), // TODO: really a bug?
                            }
                        }

                        SpirvLvalue::Ignore => (),
                        SpirvLvalue::AccessChain(..) => unreachable!(),        
                    }
                } else {
                    self.ctxt.tcx.sess.span_warn(stmt.source_info.span, "inspirv: Unhandled stmnt as lvalue couldn't be resolved!");
                }
            }
            // Translation only
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
            StatementKind::SetDiscriminant { .. } => println!("{:?}", stmt.kind),
        }
    }

    fn trans_terminator(&mut self, terminator: &Terminator<'tcx>) {
        use rustc::mir::repr::TerminatorKind::*;
        match terminator.kind {
            Goto { ref target } => {
                self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[*target])));
            }

            Return => {
                // TODO: low: handle return value
                self.block.branch_instr =
                    Some(BranchInstruction::Return(OpReturn));
            }

            Unreachable => {
                self.block.branch_instr =
                    Some(BranchInstruction::Unreachable(OpUnreachable));
            }

            // &If { cond, targets } => { },
            // &Switch { discr, adt_def, targets } => { },
            // &SwitchInt { discr, switch_ty, values, targets } => { },
            // &Resume => { },
            // &Drop { location, target, unwind } => { },
            // &DropAndReplace { location, value, target, unwind } => { },

            Call { ref func, ref args, ref destination, .. } => {
                let func_op = self.trans_operand(func);
                match func_op {
                    SpirvOperand::FnCall(def_id) => {
                        let func_id = self.ctxt.tcx.map.as_local_node_id(def_id).expect("Function is not in local crate!");
                        let attrs = self.ctxt.parse_inspirv_attributes(self.ctxt.tcx.map.attrs(func_id));

                        let intrinsic = attrs.iter().find(|attr| match **attr {
                            InspirvAttribute::Intrinsic (..) => true,
                            _ => false,
                        });

                        println!("{:?}",intrinsic);

                        let (lvalue, next_block) = destination.clone().expect("Call without destination, interesting!");
                        let lvalue = self.ctxt.resolve_lvalue(&lvalue).map(|lvalue| self.ctxt.transform_lvalue(self.block, lvalue)).expect("Unhandled lvalue");

                        // Translate function call
                        let id = if let Some(&InspirvAttribute::Intrinsic(intrinsic)) = intrinsic {
                            self.emit_intrinsic(intrinsic, args)
                        } else {
                            panic!("Unhandled function call")  // TODO: normal function call
                        };

                        // Store return value into lvalue destination
                        match lvalue {
                            SpirvLvalue::Variable(lvalue_id, _, _) | SpirvLvalue::Return(lvalue_id, _) => {
                                self.block.emit_instruction(OpStore(lvalue_id, id, None));
                            },

                            SpirvLvalue::Ignore => (),

                            _ => self.ctxt.tcx.sess.span_err(terminator.source_info.span, "inspirv: Unhandled lvalue for call terminator!"),
                        }

                        self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[next_block])));
                    }

                    _ => bug!("Unexpected operand type, expected `FnCall` ({:?})", func_op),
                }
            },
            //

            Assert { ref target, .. } => {
                // Ignore the actual asset
                // TODO: correct behaviour? some conditions?
                self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[*target])));
            },
            
            _ => { println!("Unhandled terminator kind: {:?}", terminator.kind); }, //unimplemented!(),
        }
    }

    fn trans_operand(&mut self, operand: &Operand<'tcx>) -> SpirvOperand {
        use rustc::mir::repr::Operand::*;
        match *operand {
            Consume(ref lvalue) => {
                let lvalue = self.ctxt.resolve_lvalue(lvalue);
                if let Some(lvalue) = lvalue {
                    let lvalue = self.ctxt.transform_lvalue(self.block, lvalue);
                    SpirvOperand::Consume(lvalue)
                } else {
                    println!("Unable to resolve rvalue operand {:?}", lvalue);
                    SpirvOperand::None
                }
            }

            Constant(ref c) => {
                match c.literal {
                    Literal::Item { def_id, .. } => {
                        SpirvOperand::FnCall(def_id)
                    }
                    Literal::Value { ref value } => {
                        let (constant, ty) = match *value {
                            Float(ConstFloat::F32(v)) => (module::Constant::Float(ConstValueFloat::F32(v)), Type::Float(32)),
                            Float(ConstFloat::F64(v)) => (module::Constant::Float(ConstValueFloat::F64(v)), Type::Float(64)),
                            Float(ConstFloat::FInfer { .. }) => bug!("MIR must not use `{:?}`", c.literal),
                            Integral(ConstInt::I8(..)) => bug!("Inspirv: `i8` are not supported for shaders `{:?}`", c.literal),
                            Integral(ConstInt::I16(v)) => (module::Constant::Scalar(ConstValue::I16(v)), Type::Int(16, true)),
                            Integral(ConstInt::I32(v)) => (module::Constant::Scalar(ConstValue::I32(v)), Type::Int(32, true)),
                            Integral(ConstInt::I64(v)) => (module::Constant::Scalar(ConstValue::I64(v)), Type::Int(64, true)),
                            Integral(ConstInt::Isize(_v)) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Integral(ConstInt::U8(..)) => bug!("Inspirv: `u8` are not supported for shaders `{:?}`", c.literal),
                            Integral(ConstInt::U16(v)) => (module::Constant::Scalar(ConstValue::U16(v)), Type::Int(16, false)),
                            Integral(ConstInt::U32(v)) => (module::Constant::Scalar(ConstValue::U32(v)), Type::Int(32, false)),
                            Integral(ConstInt::U64(v)) => (module::Constant::Scalar(ConstValue::U64(v)), Type::Int(64, false)),
                            Integral(ConstInt::Usize(_v)) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Bool(val) => (module::Constant::Scalar(ConstValue::Bool(val)), Type::Bool),
                            Char(_val) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Integral(ConstInt::Infer(_))
                            | Integral(ConstInt::InferSigned(_)) => bug!("MIR must not use `{:?}`", c.literal),
                            Str(_) => bug!("Currently unsupported constant literal `{:?}`", c.literal), // TODO: unsupported
                            ByteStr(ref _v) => bug!("Currently unsupported constant literal `{:?}`", c.literal), // TODO: unsupported?
                            Struct(_)
                            | Tuple(_)
                            | Array(..)
                            | Repeat(..)
                            | Function(_) => bug!("MIR must not use `{:?}` (which refers to a local ID)", c.literal),
                            Dummy => bug!(),
                        };

                        let constant_id = self.ctxt.builder.define_constant(constant);
                        SpirvOperand::Constant(constant_id, ty)
                    }
                    Literal::Promoted { .. /* ref index */ } => SpirvOperand::None,
                }
            }
        }
    }

    fn emit_binop(&mut self, op: BinOp, (result_id, result_ty): TypedId, (left_id, left_ty): TypedId, (right_id, right_ty): TypedId) {
        let left_ptr_id = self.ctxt.builder.alloc_id();
        let right_ptr_id = self.ctxt.builder.alloc_id();

        // load variable values
        let op_load_left = OpLoad(self.ctxt.builder.define_type(&left_ty), left_ptr_id, left_id, None);
        let op_load_right = OpLoad(self.ctxt.builder.define_type(&right_ty), right_ptr_id, right_id, None);
        self.block.emit_instruction(op_load_left);
        self.block.emit_instruction(op_load_right);

        // emit addition instruction
        let add_result = self.ctxt.builder.alloc_id();
        let op_binop: instruction::Instruction = match (op, &left_ty, &right_ty) {
            (BinOp::Add, &Type::Int(..), &Type::Int(..)) => {
                OpIAdd(self.ctxt.builder.define_type(&result_ty), add_result, left_ptr_id, right_ptr_id).into()
            }

            (BinOp::Add, &Type::Float(..), &Type::Float(..)) => {
                OpFAdd(self.ctxt.builder.define_type(&result_ty), add_result, left_ptr_id, right_ptr_id).into()
            }

            (BinOp::Div, &Type::Float(..), &Type::Float(..)) => {
                OpFDiv(self.ctxt.builder.define_type(&result_ty), add_result, left_ptr_id, right_ptr_id).into()
            }

            _ => bug!("Unexpected binop combination ({:?})", (op, left_ty, right_ty)),
        };

        self.block.emit_instruction(op_binop);
        
        // store
        self.block.emit_instruction(OpStore(result_id, add_result, None));
    }

    fn emit_intrinsic(&mut self, intrinsic: Intrinsic, args: &[Operand<'tcx>]) -> Id {
        use self::Intrinsic::*;
        let args_ops = args.iter().map(|arg| self.trans_operand(arg)).collect::<Vec<_>>();
        let component_ids = args_ops.iter().filter_map(
                                |arg| match *arg {
                                    SpirvOperand::Constant(c, _) => Some(c),
                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, ref op_ty, _)) => {
                                        let op_id = self.ctxt.builder.alloc_id();
                                        let op_load = OpLoad(self.ctxt.builder.define_type(op_ty), op_id, op_ptr_id, None);
                                        self.block.emit_instruction(op_load);
                                        Some(op_id)
                                    }
                                    _ => None
                                }).collect::<Vec<_>>();

        match intrinsic {
            VectorNew { components } => self.emit_intrinsic_vector_new(components, args_ops, component_ids),
            Swizzle { components_out, components_in } => self.emit_instrinsic_swizzle(
                                                                    components_in,
                                                                    components_out,
                                                                    args,
                                                                    args_ops,
                                                                    component_ids,
                                                              ),
            Shuffle { components_out:4 , components_in0: 4, components_in1: 4 } => {
                let ty = Type::Vector(Box::new(Type::Float(32)), 4);
                if args_ops[2..].iter().all(|arg| arg.is_constant()) {
                    // all args are constants!
                    let result_id = self.ctxt.builder.alloc_id();
                    // components
                    let comp_x = self.ctxt.extract_u32_from_operand(&args[2]);
                    if comp_x >= 8 { bug!{"inspirv: shuffle component `x` out of range {:?}", comp_x} }
                    let comp_y = self.ctxt.extract_u32_from_operand(&args[3]);
                    if comp_y >= 8 { bug!{"inspirv: shuffle component `y` out of range {:?}", comp_y} }
                    let comp_z = self.ctxt.extract_u32_from_operand(&args[4]);
                    if comp_z >= 8 { bug!{"inspirv: shuffle component `z` out of range {:?}", comp_z} }
                    let comp_w = self.ctxt.extract_u32_from_operand(&args[5]);
                    if comp_w >= 8 { bug!{"inspirv: shuffle component `w` out of range {:?}", comp_w} }
                    self.block.emit_instruction(
                        OpVectorShuffle(
                            self.ctxt.builder.define_type(&ty),
                            result_id,
                            component_ids[0],
                            component_ids[1],
                            vec![
                                LiteralInteger(comp_x),
                                LiteralInteger(comp_y),
                                LiteralInteger(comp_z),
                                LiteralInteger(comp_w),
                            ],
                        )
                    );
                    result_id
                } else {
                    panic!("Unhandled dynamic `shuffle4`")
                }
            }
            _ => bug!("Unknown function call intrinsic")
        }
    }

    fn emit_intrinsic_vector_new(&mut self, num_components: u32, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> Id {
        assert!(num_components as usize == component_ids.len());
        let ty = Type::Vector(Box::new(Type::Float(32)), num_components as u32);
        if args.iter().all(|arg| arg.is_constant()) {
            // all args are constants!
            let constant = module::Constant::Composite(ty, component_ids);
            self.ctxt.builder.define_constant(constant)
        } else {
            let composite_id = self.ctxt.builder.alloc_id();
            self.block.emit_instruction(
                OpCompositeConstruct(self.ctxt.builder.define_type(&ty), composite_id, component_ids)
            );
            composite_id
        }
    }

    fn emit_instrinsic_swizzle(&mut self, num_input_components: u32, num_output_components: u32, args: &[Operand<'tcx>], args_ops: Vec<SpirvOperand>, component_ids: Vec<Id>) -> Id {
        assert!(num_output_components as usize == component_ids.len());
        let ty = Type::Vector(Box::new(Type::Float(32)), num_output_components as u32);
        if args_ops[1..].iter().all(|arg| arg.is_constant()) {
            // all args are constants!
            let result_id = self.ctxt.builder.alloc_id();
            // components
            let components = (0..num_output_components as usize).map(|i| {
                let component = self.ctxt.extract_u32_from_operand(&args[i+1]);
                if component >= num_input_components as u32 {
                    bug!{"inspirv: swizzle component({:?}) out of range {:?}", i, component}
                }
                LiteralInteger(component)
            }).collect::<Vec<_>>();
            self.block.emit_instruction(
                OpVectorShuffle(
                    self.ctxt.builder.define_type(&ty),
                    result_id,
                    component_ids[0],
                    component_ids[0],
                    components
                )
            );
            result_id
        } else {
            panic!("Unhandled dynamic swizzle!")
        }
    }
}

fn extract_attr_str(lit: &syntax::ast::Lit) -> syntax::parse::token::InternedString {
    match lit.node {
        syntax::ast::LitKind::Str(ref s, _) => s.clone(),
        _ => panic!("attribute values need to be strings"),
    }
}
