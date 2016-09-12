
use rustc_mir as mir;
use rustc::mir::transform::MirSource;
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal;
use rustc_const_math::{ConstInt, ConstFloat};
use rustc::ty::{self, TyCtxt, Ty};
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::util::common::time;
use rustc_borrowck as borrowck;
use rustc_data_structures::indexed_vec::{Idx, IndexVec};
use syntax;
use syntax::ast::{NodeId, IntTy, UintTy, FloatTy, MetaItemKind, NestedMetaItemKind};
use std::collections::HashMap;
use std::fs::File;
use monomorphize;
use inspirv;
use inspirv::types::*;
use inspirv::core::instruction as core_instruction;
use inspirv::core::enumeration::*;
use inspirv::instruction::{Instruction, BranchInstruction};
use inspirv_builder::function::{Argument, LocalVar, Block};
use inspirv_builder::module::{self, Type, ModuleBuilder, ConstValue, ConstValueFloat};

// const SOURCE_INSPIRV_RUST: u32 = 0xCC; // TODO: might get an official number in the future?
const VERSION_INSPIRV_RUST: u32 = 0x00010000; // |major(1 byte)|minor(1 byte)|patch(2 byte)|

#[derive(Clone, Debug)]
enum InspirvAttribute {
    Interface,
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
    Intrinsic {
        name: String,
    },
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
         move || trans_crate(tcx, &mir_map, analysis));
}

fn trans_crate<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>,
                         mir_map: &MirMap<'tcx>,
                         analysis: &ty::CrateAnalysis) {
    let mut builder = ModuleBuilder::new();
    builder.with_source(SourceLanguage::SourceLanguageUnknown, VERSION_INSPIRV_RUST);

    let mut v = InspirvModuleCtxt {
        tcx: &tcx,
        mir_map: mir_map,
        builder: builder,

        arg_ids: IndexVec::new(),
        var_ids: IndexVec::new(),
        temp_ids: IndexVec::new(),
        return_ids: None,
    };

    v.trans();
}

#[derive(Clone, Debug)]
enum SpirvOperand {
    Consume(SpirvLvalue),
    Constant(Id),
    FnCall(DefId),
    None, // TODO: temp
}

#[derive(Clone, Debug)]
enum SpirvLvalue {
    Variable(Id, Type, StorageClass),
    Interface(Vec<(Id, Type)>, StorageClass),
    AccessChain(Id, StorageClass, Vec<Id>, Type),
    Return(Id, Type),
    Ignore, // Ignore this lvalue, e.g. return = ()
}

#[derive(Clone)]
enum FuncArg {
    Argument(Argument),
    Interface(Vec<(Id, Type)>),
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
                                                let stage = match &*extract_attr_str(value) {
                                                    "vertex" => Some(ExecutionModel::ExecutionModelVertex),
                                                    "tessellation_control" => Some(ExecutionModel::ExecutionModelTessellationControl),
                                                    "tessellation_eval" => Some(ExecutionModel::ExecutionModelTessellationEvaluation),
                                                    "geometry" => Some(ExecutionModel::ExecutionModelGeometry),
                                                    "fragment" => Some(ExecutionModel::ExecutionModelFragment),
                                                    "gl_compute" => Some(ExecutionModel::ExecutionModelGLCompute),
                                                    "kernel" => Some(ExecutionModel::ExecutionModelKernel),
                                                    _ => {
                                                        self.tcx.sess.span_err(item.span, "Unknown `inspirv` entry_point execution model");
                                                        None
                                                    },
                                                };

                                                if let Some(stage) = stage {
                                                    attrs.push(InspirvAttribute::EntryPoint { stage: stage, execution_modes: HashMap::new(), });
                                                }
                                            },

                                            "location" => {
                                                match value.node {
                                                    syntax::ast::LitKind::Int(b, _) if b >= 0 => attrs.push(InspirvAttribute::Location { location: b }),
                                                    _ => panic!("attribute value need to be valid interger"),
                                                };
                                            },

                                            "builtin" => {
                                                let builtin = match &*extract_attr_str(value) {
                                                    // Should be all possible builtIn's for shaders 
                                                    "Position" => Some(BuiltIn::BuiltInPosition),
                                                    "PointSize" => Some(BuiltIn::BuiltInPointSize),
                                                    "ClipDistance" => Some(BuiltIn::BuiltInClipDistance),
                                                    "CullDistance" => Some(BuiltIn::BuiltInCullDistance),
                                                    "VertexId" => Some(BuiltIn::BuiltInVertexId),
                                                    "InstanceId" => Some(BuiltIn::BuiltInInstanceId),
                                                    "PrimitiveId" => Some(BuiltIn::BuiltInPrimitiveId),
                                                    "Layer" => Some(BuiltIn::BuiltInLayer),
                                                    "InvocationId" => Some(BuiltIn::BuiltInInvocationId),
                                                    "ViewportIndex" => Some(BuiltIn::BuiltInViewportIndex),
                                                    "TessLevelOuter" => Some(BuiltIn::BuiltInTessLevelOuter),
                                                    "TessLevelInner" => Some(BuiltIn::BuiltInTessLevelInner),
                                                    "TessCoord" => Some(BuiltIn::BuiltInTessCoord),
                                                    "PatchVertices" => Some(BuiltIn::BuiltInPatchVertices),
                                                    "FragCoord" => Some(BuiltIn::BuiltInFragCoord),
                                                    "PointCoord" => Some(BuiltIn::BuiltInPointCoord),
                                                    "FrontFacing" => Some(BuiltIn::BuiltInFrontFacing),
                                                    "SampleId" => Some(BuiltIn::BuiltInSampleId),
                                                    "SamplePosition" => Some(BuiltIn::BuiltInSamplePosition),
                                                    "SampleMask" => Some(BuiltIn::BuiltInSampleMask),
                                                    "FragDepth" => Some(BuiltIn::BuiltInFragDepth),
                                                    "HelperInvocation" => Some(BuiltIn::BuiltInHelperInvocation),
                                                    "NumWorkgroups" => Some(BuiltIn::BuiltInNumWorkgroups),
                                                    "WorkgroupSize" => Some(BuiltIn::BuiltInWorkgroupSize),
                                                    "WorkgroupId" => Some(BuiltIn::BuiltInWorkgroupId),
                                                    "LocalInvocationId" => Some(BuiltIn::BuiltInLocalInvocationId),
                                                    "GlobalInvocationId" => Some(BuiltIn::BuiltInGlobalInvocationId),
                                                    "LocalInvocationIndex" => Some(BuiltIn::BuiltInLocalInvocationIndex),
                                                    "VertexIndex" => Some(BuiltIn::BuiltInVertexIndex),
                                                    "InstanceIndex" => Some(BuiltIn::BuiltInInstanceIndex),
                                                    _ => {
                                                        self.tcx.sess.span_err(item.span, "Unknown `inspirv` builtin variable");
                                                        None
                                                    },
                                                };

                                                if let Some(builtin) = builtin {
                                                    attrs.push(InspirvAttribute::Builtin { builtin: builtin });
                                                }
                                            },

                                            "intrinsic" => {
                                                attrs.push(InspirvAttribute::Intrinsic { name: (*extract_attr_str(value)).to_string() });
                                            },

                                            _ => {
                                                self.tcx.sess.span_err(item.span,
                                                                       "Unknown `inspirv` \
                                                                        attribute name value item")
                                            }
                                        }
                                    },
                                    MetaItemKind::Word(ref name) => {
                                        match &**name {
                                            "compiler_builtin" => attrs.push(InspirvAttribute::CompilerBuiltin),
                                            "interface" => attrs.push(InspirvAttribute::Interface),
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
                                                                                _ => panic!("attribute value need to be interger"),
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

                _ => (), // ignore non `#[inspirv(..)]` attributes
            }
        }

        attrs
    }

    // TODO: remove ugly clones..
    fn resolve_lvalue(&mut self, lvalue: &Lvalue<'tcx>) -> Option<SpirvLvalue> {
        match *lvalue {
            Lvalue::Arg(id) => {
                if let Some(arg) = self.arg_ids[id].clone() {
                    match arg {
                        FuncArg::Argument(arg) => Some(SpirvLvalue::Variable(arg.id, arg.ty, StorageClass::StorageClassFunction)),
                        FuncArg::Interface(interfaces) => Some(SpirvLvalue::Interface(interfaces, StorageClass::StorageClassInput)),
                    }
                } else {
                    Some(SpirvLvalue::Ignore) // unnamed argument `_`
                }
            }
            Lvalue::Var(id) => {
                let var = self.var_ids[id].clone();
                Some(SpirvLvalue::Variable(var.id, var.ty, StorageClass::StorageClassFunction))
            }
            Lvalue::Temp(id) => {
                let var = self.temp_ids[id].clone();
                Some(SpirvLvalue::Variable(var.id, var.ty, StorageClass::StorageClassFunction))
            }
            Lvalue::ReturnPointer => {
                match self.return_ids {
                    Some(FuncReturn::Return(ref var)) => Some(SpirvLvalue::Return(var.id, var.ty.clone())),
                    Some(FuncReturn::Interface(ref interfaces)) => Some(SpirvLvalue::Interface(interfaces.clone(), StorageClass::StorageClassOutput)),
                    None => Some(SpirvLvalue::Ignore),
                }
            },
            Lvalue::Static(def_id) => None,
            Lvalue::Projection(ref proj) => {
                if let Some(base) = self.resolve_lvalue(&proj.base) {
                    match (&proj.elem, base) {
                        (&ProjectionElem::Field(field, _), SpirvLvalue::Interface(ref interfaces, storage_class)) => {
                            let var = interfaces[field.index()].clone();
                            Some(SpirvLvalue::Variable(var.0, var.1, storage_class))
                        }
                        (&ProjectionElem::Field(field, ty), SpirvLvalue::Variable(id, _, storage_class)) => {
                            let field_id = self.builder.define_constant(module::Constant::Scalar(ConstValue::U32(field.index() as u32)));
                            Some(SpirvLvalue::AccessChain(id, storage_class, vec![field_id], self.rust_ty_to_inspirv(ty)))
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            },
        }
    }

    fn transform_lvalue(&mut self, block: &mut Block, lvalue: SpirvLvalue) -> SpirvLvalue {
        match lvalue {
            SpirvLvalue::AccessChain(root_id, storage_class, ref chain, ref ty) => {
                let chain_id = self.builder.alloc_id();
                block.instructions.push(core_instruction::OpAccessChain(
                    self.builder.define_type(&Type::Pointer(Box::new(ty.clone()), storage_class)),
                    chain_id,
                    root_id,
                    chain.clone()
                ).into());
                SpirvLvalue::Variable(chain_id, ty.clone(), storage_class)
            },
            _ => lvalue
        }
    }

    fn trans_operand(&mut self, block: &mut Block, operand: &Operand<'tcx>) -> SpirvOperand {
        match *operand {
            Operand::Consume(ref lvalue) => {
                let lvalue = self.resolve_lvalue(lvalue);
                if let Some(lvalue) = lvalue {
                    let lvalue = self.transform_lvalue(block, lvalue);
                    SpirvOperand::Consume(lvalue)
                } else {
                    println!("Unable to resolve rvalue operand {:?}", lvalue);
                    SpirvOperand::None
                }
            }

            Operand::Constant(ref c) => {
                match c.literal {
                    Literal::Item { def_id, .. } => {
                        SpirvOperand::FnCall(def_id)
                    }
                    Literal::Value { ref value } => {
                        match *value {
                            ConstVal::Float(ConstFloat::F32(v)) => SpirvOperand::Constant(self.builder.define_constant(module::Constant::Float(ConstValueFloat::F32(v)))),
                            ConstVal::Float(ConstFloat::F64(v)) => SpirvOperand::Constant(self.builder.define_constant(module::Constant::Float(ConstValueFloat::F64(v)))),
                            ConstVal::Float(ConstFloat::FInfer { .. }) => {
                                bug!("MIR must not use `{:?}`", c.literal)
                            }
                            ConstVal::Integral(ConstInt::I8(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::I8(v))))
                            }
                            ConstVal::Integral(ConstInt::I16(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::I16(v))))
                            }
                            ConstVal::Integral(ConstInt::I32(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::I32(v))))
                            }
                            ConstVal::Integral(ConstInt::I64(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::I64(v))))
                            }
                            ConstVal::Integral(ConstInt::Isize(v)) => SpirvOperand::None,
                            // {
                            // SpirvOperand::Constant(self.builder.define_constant(module::Constant::Scalar(ConstValue::Isize(v))))
                            // },
                            ConstVal::Integral(ConstInt::U8(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::U8(v))))
                            }
                            ConstVal::Integral(ConstInt::U16(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::U16(v))))
                            }
                            ConstVal::Integral(ConstInt::U32(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::U32(v))))
                            }
                            ConstVal::Integral(ConstInt::U64(v)) => {
                                SpirvOperand::Constant(self.builder
                                    .define_constant(module::Constant::Scalar(ConstValue::U64(v))))
                            }
                            ConstVal::Integral(ConstInt::Usize(v)) => SpirvOperand::None,
                            // {
                            // SpirvOperand::Constant(self.builder.define_constant(module::Constant::Scalar(ConstValue::Usize(v))))
                            // },
                            ConstVal::Bool(val) => SpirvOperand::Constant(self.builder.define_constant(module::Constant::Scalar(ConstValue::Bool(val)))),
                            ConstVal::Char(val) => SpirvOperand::None,
                            ConstVal::Integral(ConstInt::Infer(_)) |
                            ConstVal::Integral(ConstInt::InferSigned(_)) => {
                                bug!("MIR must not use `{:?}`", c.literal)
                            }
                            ConstVal::Str(ref v) => SpirvOperand::None, // TODO: unsupported
                            ConstVal::ByteStr(ref v) => SpirvOperand::None, // TODO: unsupported?
                            ConstVal::Struct(_) |
                            ConstVal::Tuple(_) |
                            ConstVal::Array(..) |
                            ConstVal::Repeat(..) |
                            ConstVal::Function(_) => {
                                bug!("MIR must not use `{:?}` (which refers to a local ID)",
                                     c.literal)
                            }
                            ConstVal::Dummy => bug!(),
                        }
                    }
                    Literal::Promoted { ref index } => SpirvOperand::None,
                }
            }
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
            if attrs.iter().any(|attr| match attr { &InspirvAttribute::CompilerBuiltin | &InspirvAttribute::Intrinsic {..} => true, _ => false }) {
                return;
            }

            let fn_name = &*self.tcx.map.name(id).as_str();

            // check if we have an entry point
            let entry_point = attrs.iter().find(|attr| match *attr {
                &InspirvAttribute::EntryPoint { .. } => true,
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
                } else {
                    // TODO: low-mid: unsafe! We would like to find the attributes of the current type
                    // Dont know how to correctly retrieve this information for non-local crates!
                    if let Some(ty_id) = arg.ty.ty_to_def_id() {
                        let node_id = self.tcx.map.as_local_node_id(ty_id).unwrap();
                        let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));

                        let interface = attrs.iter().find(|attr| match *attr {
                            &InspirvAttribute::Interface => true,
                            _ => false,
                        });

                        if let Some(&InspirvAttribute::Interface) = interface {
                            if let ty::TyStruct(ref adt, ref subs) = arg.ty.sty {
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
                                        if let hir::map::Node::NodeItem(ref item) = node {
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
                        } else {
                            // Entry Point Handling
                            // These functions don't have actual input/output parameters
                            // We use them for the shader interface and uniforms
                            if entry_point.is_some() {
                                bug!("Input argument type requires interface attribute({:?})", arg.ty)
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
                        }
                    } else {
                        if entry_point.is_some() {
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
                    ty::TyStruct(ref adt, ref subs) => {
                        if let Some(ty_id) = mir.return_ty.ty_to_def_id() {
                            let node_id = self.tcx.map.as_local_node_id(ty_id).unwrap();
                            let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));

                            let interface = attrs.iter().find(|attr| match *attr {
                                &InspirvAttribute::Interface => true,
                                _ => false,
                            });

                            if let Some(&InspirvAttribute::Interface) = interface {
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
                                        if let hir::map::Node::NodeItem(ref item) = node {
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

                // Define entry point in SPIR-V
                let mut func = self.builder
                    .define_entry_point(fn_name, stage, execution_modes.clone(), interface_ids)
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
        for (i, _) in mir.basic_blocks().iter().enumerate() {
            let block = fn_module.add_block(self.builder.alloc_id());
            block_labels.push(block.label);
        }

        for (i, bb) in mir.basic_blocks().iter().enumerate() {
            println!("bb{}: {:#?}", i, bb);

            let mut block = &mut fn_module.blocks[i];

            for stmt in &bb.statements {
                match stmt.kind {
                    StatementKind::Assign(ref lvalue, ref rvalue) => {
                        println!("{:?}", (lvalue, rvalue));
                        
                        if let Some(lvalue) = self.resolve_lvalue(lvalue) {
                            let lvalue = self.transform_lvalue(block, lvalue);
                        
                            match lvalue {
                                SpirvLvalue::Variable(lvalue_id, lvalue_ty, _) | SpirvLvalue::Return(lvalue_id, lvalue_ty) => {
                                    match *rvalue {
                                        Rvalue::Use(ref operand) => {
                                            let op = self.trans_operand(block, operand);
                                            match op {
                                                SpirvOperand::Constant(op_id) => {
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, op_id, None).into());
                                                }
                                                SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                                    let op_id = self.builder.alloc_id();
                                                    block.instructions.push(core_instruction::OpLoad(self.builder.define_type(&op_ty), op_id, op_ptr_id, None).into());
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, op_id, None).into());
                                                }
                                                SpirvOperand::Consume(SpirvLvalue::Interface(ref interfaces, _)) => {
                                                    let ids = interfaces.iter().map(|interface| {
                                                        let id = self.builder.alloc_id();
                                                        block.instructions.push(core_instruction::OpLoad(self.builder.define_type(&interface.1), id, interface.0, None).into());
                                                        id
                                                    }).collect::<Vec<_>>();
                                                    let composite_id = self.builder.alloc_id();
                                                    block.instructions.push(core_instruction::OpCompositeConstruct(self.builder.define_type(&lvalue_ty), composite_id, ids).into());
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, composite_id, None).into());
                                                }
                                                _ => self.tcx.sess.span_err(stmt.source_info.span,
                                                                   "inspirv: Unsupported rvalue!"),
                                            }
                                        }

                                        /// [x; 32]
                                        Rvalue::Repeat(ref operand, ref times) => {}

                                        Rvalue::Ref(_, _, _) => {
                                            self.tcx.sess.span_err(stmt.source_info.span,
                                                                   "inspirv: Unsupported rvalue reference!")
                                        }

                                        /// length of a [X] or [X;n] value
                                        Rvalue::Len(ref val) => {}

                                        Rvalue::Cast(ref kind, ref operand, ref ty) => {}

                                        Rvalue::BinaryOp(ref op, ref left, ref right) |
                                        Rvalue::CheckedBinaryOp(ref op, ref left, ref right) => {
                                            let left = self.trans_operand(block, left);
                                            let right = self.trans_operand(block, right);
                                            println!("binop: {:?}", op);

                                            match (left, right) {
                                                (SpirvOperand::Consume(SpirvLvalue::Variable(left_ptr_id,
                                                                       Type::Int(left_width, left_sign), _)),
                                                 SpirvOperand::Consume(SpirvLvalue::Variable(right_ptr_id,
                                                                       Type::Int(right_width, right_sign), _))) => {
                                                    let left_id = self.builder.alloc_id();
                                                    let right_id = self.builder.alloc_id();

                                                    // load variable values
                                                    block.instructions
                                                        .push(core_instruction::OpLoad(
                                                            self.builder.define_type(&Type::Int(left_width, left_sign)),
                                                            left_id,
                                                            left_ptr_id,
                                                            None
                                                        ).into());

                                                    block.instructions
                                                        .push(core_instruction::OpLoad(
                                                            self.builder.define_type(&Type::Int(right_width, right_sign)),
                                                            right_id,
                                                            right_ptr_id,
                                                            None
                                                        ).into());

                                                    // emit addition instruction
                                                    let add_result = self.builder.alloc_id();
                                                    block.instructions.push(core_instruction::OpIAdd(self.builder.define_type(&lvalue_ty), add_result, left_id, right_id).into());
                                                    // store
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, add_result, None).into());
                                                }

                                                // TODO:
                                                _ => (),
                                            }
                                        }

                                        Rvalue::UnaryOp(ref op, ref operand) => {
                                            let operand = self.trans_operand(block, operand);
                                            println!("unop: {:?}", op);
                                        }

                                        Rvalue::Aggregate(ref kind, ref operands) => {}

                                        Rvalue::Box(..) => {
                                            self.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid box r-value")
                                        }
                                        Rvalue::InlineAsm { .. } => {
                                            self.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid inline asm")
                                        }
                                    }
                                }

                                SpirvLvalue::Interface(ref interfaces, _) => {
                                    match *rvalue {
                                        Rvalue::Use(ref _operand) => {
                                            /*
                                            let op = self.trans_operand(block, operand);
                                            match op {
                                                SpirvOperand::Constant(op_id) => {
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, op_id, None).into());
                                                }
                                                SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty)) => {
                                                    let op_id = self.builder.alloc_id();
                                                    block.instructions.push(core_instruction::OpLoad(self.builder.define_type(&op_ty), op_id, op_ptr_id, None).into());
                                                    block.instructions.push(core_instruction::OpStore(lvalue_id, op_id, None).into());
                                                }
                                                SpirvOperand::Consume(SpirvLvalue::Interface(..)) => self.tcx.sess.span_err(stmt.source_info.span,
                                                                   "inspirv: Unsupported rvalue interface (so far)!"),
                                                _ => self.tcx.sess.span_err(stmt.source_info.span,
                                                                   "inspirv: Unsupported rvalue!"),
                                            }
                                            */
                                            self.tcx.sess.span_warn(stmt.source_info.span,
                                                        "inspirv: Unhandled assignment for interfaces (soon)!")
                                        }

                                        Rvalue::Aggregate(ref kind, ref operands) => {
                                            for (operand, interface) in operands.iter().zip(interfaces.iter()) {
                                                let op = self.trans_operand(block, operand);
                                                match op {
                                                    SpirvOperand::Constant(op_id) => {
                                                        block.instructions.push(core_instruction::OpStore(interface.0, op_id, None).into());
                                                    }
                                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                                        let op_id = self.builder.alloc_id();
                                                        block.instructions.push(core_instruction::OpLoad(self.builder.define_type(&op_ty), op_id, op_ptr_id, None).into());
                                                        block.instructions.push(core_instruction::OpStore(interface.0, op_id, None).into());
                                                    }
                                                    _ => self.tcx.sess.span_err(stmt.source_info.span,
                                                                       "inspirv: Unsupported aggregate operand!"),
                                                }
                                            }
                                        }

                                        _ => bug!("Unexpected rvalue for an interface ({:?})", rvalue), // TODO: really a bug?
                                    }
                                }

                                SpirvLvalue::Ignore => (),
                                SpirvLvalue::AccessChain(root_id, storage_class, chain, ty) => unreachable!(),        
                            }
                        } else {
                            self.tcx.sess.span_warn(stmt.source_info.span, "inspirv: Unhandled stmnt as lvalue couldn't be resolved!");
                        }
                    }
                    // Translation only
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                    StatementKind::SetDiscriminant { .. } => println!("{:?}", stmt.kind),
                }
            }

            match &bb.terminator().kind {
                &TerminatorKind::Goto { ref target } => {
                    block.branch_instr = Some(BranchInstruction::Branch(core_instruction::OpBranch(block_labels[*target])));
                }

                &TerminatorKind::Return => {
                    // TODO: low: handle return value
                    block.branch_instr =
                        Some(BranchInstruction::Return(core_instruction::OpReturn));
                }

                &TerminatorKind::Unreachable => {
                    block.branch_instr =
                        Some(BranchInstruction::Unreachable(core_instruction::OpUnreachable));
                }

                // &TerminatorKind::If { cond, targets } => {
                //
                // },
                //
                // &TerminatorKind::Switch { discr, adt_def, targets } => {
                //
                // },
                //
                // &TerminatorKind::SwitchInt { discr, switch_ty, values, targets } => {
                //
                // },
                //
                // &TerminatorKind::Resume => {
                //
                // },
                //
                // &TerminatorKind::Drop { location, target, unwind } => {
                //
                // },
                //
                // &TerminatorKind::DropAndReplace { location, value, target, unwind } => {
                //
                // },
                //
                &TerminatorKind::Call { ref func, ref args, ref destination, .. } => {
                    let func_op = self.trans_operand(block, func);
                    match func_op {
                        SpirvOperand::FnCall(def_id) => {
                            let func_id = self.tcx.map.as_local_node_id(def_id).expect("Function is not in local crate!");
                            let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(func_id));

                            let intrinsic = attrs.iter().find(|attr| match *attr {
                                &InspirvAttribute::Intrinsic { .. } => true,
                                _ => false,
                            });

                            println!("{:?}",intrinsic);

                            let (lvalue, next_block) = destination.clone().expect("Call without destination, interesting!");
                            let lvalue =  self.resolve_lvalue(&lvalue).map(|lvalue| self.transform_lvalue(block, lvalue)).expect("Unhandled lvalue");

                            let args_ops = args.iter().map(|arg| self.trans_operand(block, arg)).collect::<Vec<_>>();
                            let const_only = args_ops.iter().all(|arg| match arg { &SpirvOperand::Constant(..) => true, _ => false });
                            let component_ids = args_ops.iter().filter_map(
                                                    |arg| match arg {
                                                        &SpirvOperand::Constant(c) => Some(c),
                                                        &SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, ref op_ty, _)) => {
                                                            let op_id = self.builder.alloc_id();
                                                            block.instructions.push(
                                                                core_instruction::OpLoad(self.builder.define_type(op_ty), op_id, op_ptr_id, None).into()
                                                            );
                                                            Some(op_id)
                                                        }
                                                        _ => None
                                                    }).collect::<Vec<_>>();

                            // Translate function call
                            let id = if let Some(&InspirvAttribute::Intrinsic { ref name }) = intrinsic {
                                // Explicit handling of intrinsic functions!
                                match name.as_str() {
                                    "float2_new" => {
                                        let ty = Type::Vector(Box::new(Type::Float(32)), 2);
                                        if const_only {
                                            self.builder.define_constant(
                                                module::Constant::Composite(
                                                    ty,
                                                    component_ids,
                                                )
                                            )
                                        } else {
                                            let composite_id = self.builder.alloc_id();
                                            block.instructions.push(
                                                core_instruction::OpCompositeConstruct(self.builder.define_type(&ty), composite_id, component_ids).into()
                                            );
                                            composite_id
                                        }
                                    },

                                    "float3_new" => {
                                        let ty = Type::Vector(Box::new(Type::Float(32)), 3);
                                        if const_only {
                                            self.builder.define_constant(
                                                module::Constant::Composite(
                                                    ty,
                                                    component_ids,
                                                )
                                            )
                                        } else {
                                            let composite_id = self.builder.alloc_id();
                                            block.instructions.push(
                                                core_instruction::OpCompositeConstruct(self.builder.define_type(&ty), composite_id, component_ids).into()
                                            );
                                            composite_id
                                        }
                                    },

                                    "float4_new" => {
                                        let ty = Type::Vector(Box::new(Type::Float(32)), 4);
                                        if const_only {
                                            self.builder.define_constant(
                                                module::Constant::Composite(
                                                    ty,
                                                    component_ids,
                                                )
                                            )
                                        } else {
                                            let composite_id = self.builder.alloc_id();
                                            block.instructions.push(
                                                core_instruction::OpCompositeConstruct(self.builder.define_type(&ty), composite_id, component_ids).into()
                                            );
                                            composite_id
                                        }
                                    },

                                    _ => bug!("Unknown function call intrinsic"),
                                }
                            } else {
                                panic!("Unhandled function call")  // TODO: normal function call
                            };

                            // Store return value into lvalue destination
                            match lvalue {
                                SpirvLvalue::Variable(lvalue_id, lvalue_ty, _) | SpirvLvalue::Return(lvalue_id, lvalue_ty) => {
                                    block.instructions.push(core_instruction::OpStore(lvalue_id, id, None).into());
                                },

                                SpirvLvalue::Ignore => (),

                                _ => self.tcx.sess.span_err(bb.terminator().source_info.span, "inspirv: Unhandled lvalue for call terminator!"),
                            }

                            block.branch_instr = Some(BranchInstruction::Branch(core_instruction::OpBranch(block_labels[next_block])));
                        }

                        _ => bug!("Unexpected operand type, expected `FnCall` ({:?})", func_op),
                    }
                },
                //

                &TerminatorKind::Assert { ref target, .. } => {
                    // Ignore the actual asset
                    // TODO: correct behaviour? some conditions?
                    block.branch_instr = Some(BranchInstruction::Branch(core_instruction::OpBranch(block_labels[*target])));
                },
                
                _ => { println!("Unhandled terminator kind: {:?}", bb.terminator().kind); }, //unimplemented!(),
            }
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
            ty::TyChar => Type::Int(8, false),
            ty::TyInt(IntTy::Is) => Type::Int(32, true), // isize
            ty::TyInt(IntTy::I8) => Type::Int(8, true),
            ty::TyInt(IntTy::I16) => Type::Int(16, true),
            ty::TyInt(IntTy::I32) => Type::Int(32, true),
            ty::TyInt(IntTy::I64) => Type::Int(64, true),
            ty::TyUint(UintTy::Us) => Type::Int(32, false), // usize
            ty::TyUint(UintTy::U8) => Type::Int(8, false),
            ty::TyUint(UintTy::U16) => Type::Int(16, false),
            ty::TyUint(UintTy::U32) => Type::Int(32, false),
            ty::TyUint(UintTy::U64) => Type::Int(64, false),
            ty::TyFloat(FloatTy::F32) => Type::Float(32),
            ty::TyFloat(FloatTy::F64) => Type::Float(64),
            ty::TyArray(ty, len) => unimplemented!(),
            ty::TyTuple(&[]) => Type::Void,
            ty::TyTuple(ref tys) => Type::Struct(tys.iter().map(|ty| self.rust_ty_to_inspirv(ty)).collect()),
            ty::TyStruct(ref adt, ref subs) => {
                // TODO: low-mid: unsafe! We would like to find the attributes of the current type, to look for representations as vector/matrix
                // Dont know how to correctly retrieve this information for non-local crates!
                let node_id = self.tcx.map.as_local_node_id(adt.did).unwrap();
                let attrs = self.parse_inspirv_attributes(self.tcx.map.attrs(node_id));
                let internal_type = attrs.iter().find(|attr| match *attr {
                    &InspirvAttribute::Vector { .. } => true,
                    _ => false,
                });

                if let Some(ref internal_type) = internal_type {
                    match *internal_type {
                        &InspirvAttribute::Vector { ref base, components } => Type::Vector(base.clone(), components as u32),
                        _ => bug!("Unhandled internal type ({:?})", *internal_type),
                    }
                } else {
                    // an actual struct!
                    // TODO: handle names
                    Type::Struct(adt.struct_variant().fields.iter().map(|field| self.rust_ty_to_inspirv(field.ty(*self.tcx, subs))).collect())
                }    
            },
            ty::TyRawPtr(..) => { println!("{:?}", t.sty); unimplemented!() },

            // Some weird case, appearing sometimes in the code for whatever reason
            // Often as unused temporary variables, which are never really used
            ty::TyNever => Type::Void,

            _ => { println!("{:?}", t.sty); unimplemented!() },
            // TyEnum(AdtDef<'tcx>, &'tcx Substs<'tcx>),
            // TyBox(Ty<'tcx>),
            // TyStr,.
            // TySlice(Ty<'tcx>),
            //
            // TyRef(&'tcx Region, TypeAndMut<'tcx>),
            // TyFnDef(DefId, &'tcx Substs<'tcx>, &'tcx BareFnTy<'tcx>),
            // TyFnPtr(&'tcx BareFnTy<'tcx>),
            // TyTrait(Box<TraitTy<'tcx>>),
            // TyClosure(DefId, ClosureSubsts<'tcx>),
            // TyProjection(ProjectionTy<'tcx>),
            // TyParam(ParamTy),
            // TyInfer(InferTy),
            // TyError,
            //
        }
    }
}

fn extract_attr_str(lit: &syntax::ast::Lit) -> syntax::parse::token::InternedString {
    match lit.node {
        syntax::ast::LitKind::Str(ref s, _) => s.clone(),
        _ => panic!("attribute values need to be strings"),
    }
}
