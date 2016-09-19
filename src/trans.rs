use libc::c_char;
use error::*;
use rustc_mir as mir;
use rustc::mir::transform::MirSource;
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal;
use rustc_const_math::{ConstInt, ConstIsize, ConstFloat};
use rustc::ty::{self, TyCtxt, Ty, FnSig};
use rustc::ty::layout::{self, Layout, Size};
use rustc::ty::subst::Substs;
use rustc::hir::intravisit::{self, Visitor, FnKind};
use rustc::hir::{self, FnDecl, Block};
use rustc::hir::def_id::DefId;
use rustc::util::common::time;
use rustc_borrowck as borrowck;
use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use syntax;
use syntax::ast::{NodeId, IntTy, UintTy, FloatTy, MetaItemKind, NestedMetaItemKind};
use syntax::codemap::Span;
use std::ffi::CString;
use std::ptr;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io;
use std::fs::File;
use monomorphize;
use traits;
use inspirv;
use inspirv::types::*;
use inspirv::core::instruction as core_instruction;
use inspirv::core::enumeration::*;
use inspirv::instruction::{Instruction, BranchInstruction};
use inspirv_builder::function::{Argument, LocalVar};
use inspirv_builder::module::{self, Type, ModuleBuilder, ConstValue, ConstValueFloat};

const SOURCE_INSPIRV_RUST: u32 = 0xCC; // TODO: might get an official number in the future?
const VERSION_INSPIRV_RUST: u32 = 0x00010000; // |major(1 byte)|minor(1 byte)|patch(2 byte)|

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
        return_id: None,
    };

    v.trans();
}

enum SpirvOperand {
    Consume(Id, Type),
    Constant(Id),
    None, // TODO: temp
}

struct InspirvModuleCtxt<'v, 'tcx: 'v> {
    tcx: &'v TyCtxt<'v, 'tcx, 'tcx>,
    mir_map: &'v MirMap<'tcx>,
    builder: ModuleBuilder,

    arg_ids: IndexVec<Arg, Option<Argument>>,
    var_ids: IndexVec<Var, LocalVar>,
    temp_ids: IndexVec<Temp, LocalVar>,
    return_id: Option<LocalVar>,
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

    fn resolve_lvalue(&self, lvalue: &Lvalue<'tcx>) -> Option<(Id, Type)> {
        match *lvalue {
            Lvalue::Arg(id) => {
                let arg = self.arg_ids[id].clone().unwrap();
                Some((arg.id, arg.ty))
            }
            Lvalue::Var(id) => {
                let var = self.var_ids[id].clone();
                Some((var.id, var.ty))
            }
            Lvalue::Temp(id) => {
                let var = self.temp_ids[id].clone();
                Some((var.id, var.ty))
            }
            Lvalue::ReturnPointer => None,
            Lvalue::Static(def_id) => None,
            Lvalue::Projection(ref projection) => None,
        }
    }

    fn trans_operand(&mut self, operand: &Operand<'tcx>) -> SpirvOperand {
        match *operand {
            Operand::Consume(ref lvalue) => {
                if let Some((id, ty)) = self.resolve_lvalue(lvalue) {
                    SpirvOperand::Consume(id, ty)
                } else {
                    SpirvOperand::None
                }
            }

            Operand::Constant(ref c) => {
                match c.literal {
                    Literal::Item { .. } => SpirvOperand::None,
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

        for attr in self.tcx.map.attrs(id) {
            match attr.node.value.node {
                MetaItemKind::List(ref name, ref items) if name == "inspirv" => {
                    for item in items {
                        match item.node {
                            NestedMetaItemKind::MetaItem(ref item) => {
                                match item.node {
                                    MetaItemKind::NameValue(ref name, ref value) => {
                                        // TODO:
                                        match &**name {
                                            "storage_class" => {
                                                match &*extract_attr_str(value) {
                                                    _ => (),
                                                }
                                            }

                                            // TODO: maybe other things needed in the future?
                                            _ => {
                                                self.tcx
                                                    .sess
                                                    .span_err(item.span, "Unknown `inspirv` attribute item")
                                            }
                                        }
                                    },
                                    _ => {
                                        self.tcx
                                            .sess
                                            .span_err(item.span, "Unknown `inspirv` attribute item")
                                    }
                                }
                            },
                            _ => {
                                self.tcx
                                    .sess
                                    .span_err(item.span, "Unknown `inspirv` attribute item.")
                            }
                        }
                    }
                }

                _ => (),
            }
        }
    }

    fn trans_const(&mut self, id: NodeId, mir: &'v Mir<'tcx>) {
        println!("{:?} {:?}", id, mir);
    }

    fn trans_fn(&mut self, id: NodeId, mir: &'v Mir<'tcx>) {
        

        let (mut fn_module, arg_ids) =
            {
                // check if we have an entry point or a normal function
                let mut entry_point: Option<ExecutionModel> = None;
                let mut execution_modes: HashMap<ExecutionModeKind, ExecutionMode> = HashMap::new();
                let mut builtin = false;

                // extract all inspirv related attributes for our function
                // every attribute has to be sth like `#[inspirv(..)]
                for attr in self.tcx.map.attrs(id) {
                    match attr.node.value.node {
                        MetaItemKind::List(ref name, ref items) if name == "inspirv" => {
                            for item in items {
                                match item.node {
                                    NestedMetaItemKind::MetaItem(ref item) => {
                                        match item.node {
                                            MetaItemKind::NameValue(ref name, ref value) => {
                                                match &**name {
                                                    "entry_point" => {
                                                        match &*extract_attr_str(value) {
                                                            "vertex" => entry_point = Some(ExecutionModel::ExecutionModelVertex),
                                                            "tessellation_control" => entry_point = Some(ExecutionModel::ExecutionModelTessellationControl),
                                                            "tessellation_eval" => entry_point = Some(ExecutionModel::ExecutionModelTessellationEvaluation),
                                                            "geometry" => entry_point = Some(ExecutionModel::ExecutionModelGeometry),
                                                            "fragment" => entry_point = Some(ExecutionModel::ExecutionModelFragment),
                                                            "gl_compute" => entry_point = Some(ExecutionModel::ExecutionModelGLCompute),
                                                            "kernel" => entry_point = Some(ExecutionModel::ExecutionModelKernel),
                                                            _ => {
                                                                self.tcx.sess.span_err(item.span,
                                                                                       "Unknown `inspirv` \
                                                                                        entry_point \
                                                                                        execution model")
                                                            }
                                                        }
                                                    }

                                                    // TODO: execution modes e.g local_size(x = 5, y = 10, z = 1)
                                                    // TODO: maybe other things needed in the future? intrinsics?
                                                    _ => {
                                                        self.tcx.sess.span_err(item.span,
                                                                               "Unknown `inspirv` \
                                                                                attribute item")
                                                    }
                                                }
                                            },
                                            MetaItemKind::Word(ref name) => {
                                                match &**name {
                                                    "builtin" => builtin = true,
                                                    _ => {
                                                        self.tcx.sess.span_err(item.span,
                                                                               "Unknown `inspirv` \
                                                                                attribute item")
                                                    }
                                                }
                                            },
                                            _ => { self.tcx.sess.span_err(item.span,
                                                                               "Unknown `inspirv` \
                                                                                attribute item")
                                            }
                                        }
                                    },
                                    _ => {
                                        self.tcx.sess.span_err(item.span,
                                                               "Unknown `inspirv` attribute item.")
                                    }
                                }
                            }
                        }

                        _ => (), // println!("{:?}", attr.node.value.node),
                    }
                }

                // We don't translate builtin functions, these will be handled internally
                if builtin {
                    return;
                }

                let fn_name = &*self.tcx.map.name(id).as_str();

                if let Some(execution_model) = entry_point {
                    // TODO: better error handling

                    // Extract all arguments and store their ids in a list for faster access later
                    // entry point arguments are handled as interfaces instead of normal function arguments
                    let mut arg_ids: IndexVec<Arg, Option<Argument>> = IndexVec::new();
                    for (i, arg) in mir.arg_decls.iter().enumerate() {
                        let name = &*arg.debug_name.as_str();
                        if name.is_empty() {
                            arg_ids.push(None);
                        } else {
                            let ty = self.rust_ty_to_inspirv(arg.ty);
                            let id = self.builder
                                .define_variable(name, ty.clone(), StorageClass::StorageClassInput);
                            arg_ids.push(Some(Argument { id: id, ty: ty }));
                        }
                    }

                    // TODO: mid: split tuple types into multiple output interfaces
                    // TODO: high: We could also handle this differently by specifying all interfaces as arguments annotated with the storage storage_class
                    //      e.g. fn foo(pos: &(f32, f32, f32), color: &vec4, #[inspirv(output)] vertex_pos: &mut vec4) { .. }
                    // return types are handled as output interfaces
                    {
                        let ty = mir.return_ty;
                        {
                            let ty = self.rust_ty_to_inspirv(ty);
                            let id = self.builder
                                .define_variable(format!("{}_ret", fn_name).as_str(),
                                                 ty.clone(),
                                                 StorageClass::StorageClassOutput);
                            arg_ids.push(Some(Argument { id: id, ty: ty }));
                        }
                    }

                    let interfaces: Vec<Id> =
                        arg_ids.iter().filter_map(|arg| arg.clone().map(|arg| arg.id)).collect();

                    let mut func = self.builder
                        .define_entry_point(fn_name, execution_model, execution_modes, interfaces)
                        .ok()
                        .unwrap();

                    func.ret_ty = Type::Void;

                    (func, arg_ids)
                } else {
                    let mut func = self.builder.define_function_named(fn_name);

                    func.ret_ty = self.rust_ty_to_inspirv(mir.return_ty);

                    // Extract all arguments and store their ids in a list for faster access later
                    let mut arg_ids: IndexVec<Arg, Option<Argument>> = IndexVec::new();
                    for (i, arg) in mir.arg_decls.iter().enumerate() {
                        let name = &*arg.debug_name.as_str();
                        if name.is_empty() {
                            arg_ids.push(None);
                        } else {
                            let id = self.builder.alloc_id();
                            let arg = Argument {
                                id: id,
                                ty: self.rust_ty_to_inspirv(arg.ty),
                            };
                            func.params.push(arg.clone());
                            self.builder.name_id(id, name); // TODO: hide this behind a function module interface
                            arg_ids.push(Some(arg));
                        }
                    }

                    (func, arg_ids)
                }
            };

        println!("{:?}", (id, self.tcx.map.name(id).as_str(), mir));

        // local variables and temporaries
        let var_ids = {
            let mut ids: IndexVec<Var, LocalVar> = IndexVec::new();
            for (i, var) in mir.var_decls.iter().enumerate() {
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

        let temp_ids = {
            let mut ids: IndexVec<Temp, LocalVar> = IndexVec::new();
            for (i, var) in mir.temp_decls.iter().enumerate() {
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

        println!("{:?}", temp_ids);

        self.arg_ids = arg_ids;
        self.var_ids = var_ids;
        self.temp_ids = temp_ids;

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
                        let lvalue = self.resolve_lvalue(lvalue);

                        if lvalue.is_none() {
                            self.tcx.sess.span_warn(stmt.source_info.span,
                                                    "inspirv: Unhandled stmnt as lvalue couldn't \
                                                     be resolved!");
                            continue;
                        }

                        let lvalue_id = lvalue.clone().unwrap().0;
                        let lvalue_ty = lvalue.unwrap().1;

                        match *rvalue {
                            Rvalue::Use(ref operand) => {
                                let op = self.trans_operand(operand);
                                match op {
                                    SpirvOperand::Constant(op_id) => {
                                        block.instructions.push(Instruction::Core(core_instruction::Instruction::OpStore(core_instruction::OpStore(lvalue_id, op_id, None))));
                                    }
                                    SpirvOperand::Consume(op_ptr_id, op_ty) => {
                                        let op_id = self.builder.alloc_id();
                                        block.instructions
                                            .push(Instruction::Core(core_instruction::Instruction::OpLoad(core_instruction::OpLoad(self.builder.define_type(&op_ty), op_id, op_ptr_id, None))));
                                        block.instructions.push(Instruction::Core(core_instruction::Instruction::OpStore(core_instruction::OpStore(lvalue_id, op_id, None))));
                                    }
                                    _ => (),
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
                                let left = self.trans_operand(left);
                                let right = self.trans_operand(right);
                                println!("binop: {:?}", op);

                                match (left, right) {
                                    (SpirvOperand::Consume(left_ptr_id,
                                                           Type::Int(left_widht, left_sign)),
                                     SpirvOperand::Consume(right_ptr_id,
                                                           Type::Int(right_width, right_sign))) => {
                                        let left_id = self.builder.alloc_id();
                                        let right_id = self.builder.alloc_id();

                                        // load variable values
                                        block.instructions
                                            .push(Instruction::Core(core_instruction::Instruction::OpLoad(core_instruction::OpLoad(self.builder.define_type(&Type::Int(left_widht, left_sign)),
                                                                                                                                   left_id,
                                                                                                                                   left_ptr_id,
                                                                                                                                   None))));
                                        block.instructions
                                            .push(Instruction::Core(core_instruction::Instruction::OpLoad(core_instruction::OpLoad(self.builder.define_type(&Type::Int(right_width, right_sign)),
                                                                                                                                   right_id,
                                                                                                                                   right_ptr_id,
                                                                                                                                   None))));

                                        // emit addition instruction
                                        let add_result = self.builder.alloc_id();
                                        block.instructions.push(Instruction::Core(core_instruction::Instruction::OpIAdd(core_instruction::OpIAdd(self.builder.define_type(&lvalue_ty),
                                                                                                                                                 add_result,
                                                                                                                                                 left_id,
                                                                                                                                                 right_id))));

                                        // store
                                        block.instructions.push(Instruction::Core(core_instruction::Instruction::OpStore(core_instruction::OpStore(lvalue_id, add_result, None))));
                                    }

                                    // TODO:
                                    _ => (),
                                }
                            }

                            Rvalue::UnaryOp(ref op, ref operand) => {
                                let operand = self.trans_operand(operand);
                                println!("unop: {:?}", op);
                            }

                            Rvalue::Aggregate(ref kind, ref operands) => {}

                            Rvalue::Box(..) => {
                                self.tcx
                                    .sess
                                    .span_err(stmt.source_info.span, "inspirv: Invalid box r-value")
                            }
                            Rvalue::InlineAsm { .. } => {
                                self.tcx
                                    .sess
                                    .span_err(stmt.source_info.span, "inspirv: Invalid inline asm")
                            }
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
                // &TerminatorKind::Drop {
                // location,
                // target,
                // unwind
                // } => {
                //
                // },
                //
                // &TerminatorKind::DropAndReplace {
                // location,
                // value,
                // target,
                // unwind,
                // } => {
                //
                // },
                //
                // &TerminatorKind::Call {
                // func,
                // args,
                // destination,
                // cleanup
                // } => {
                //
                // },
                //

                &TerminatorKind::Assert { ref target, .. } => {
                    block.branch_instr = Some(BranchInstruction::Branch(core_instruction::OpBranch(block_labels[*target])));
                },
                
                _ => { println!("Unhandled terminator kind: {:?}", bb.terminator().kind); ()}, //unimplemented!(),
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
            ty::TyTuple(ref tys) => {
                Type::Struct(tys.iter().map(|ty| self.rust_ty_to_inspirv(ty)).collect())
            }
            ty::TyStruct(ref adt, ref subs) => {
                // TODO: low-mid: unsafe! We would like to find the attributes of the current type, to look for representations as vector/matrix
                // Dont know how to correctly retrieve this information for non-local crates!
                let node_id = self.tcx.map.as_local_node_id(adt.did).unwrap();
                // extract all inspirv related attributes for our function
                // every attribute has to be sth like `#[inspirv(..)]
                let mut internal_type = None;
                for attr in self.tcx.map.attrs(node_id) {
                    match attr.node.value.node {
                        MetaItemKind::List(ref name, ref items) if name == "inspirv" => {
                            for item in items {
                                match item.node {
                                    NestedMetaItemKind::MetaItem(ref item) => {
                                        match item.node {
                                            MetaItemKind::NameValue(ref name, ref value) => {
                                                match &**name {
                                                    "vector" => {
                                                        let mut base = None;
                                                        let mut components = None;
                                                        for item in items {
                                                            match item.node {
                                                                NestedMetaItemKind::MetaItem(ref item) => {
                                                                    match item.node {
                                                                        MetaItemKind::NameValue(ref name,
                                                                                                ref value) => {
                                                                            match &**name {
                                                                                "components" => {
                                                                                    components =
                                                                                        extract_attr_str(value)
                                                                                            .parse()
                                                                                            .ok()
                                                                                } // TODO: low: check > 1
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
                                                                                }

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
                                                            internal_type =
                                                                Some(Type::Vector(Box::new(base.unwrap()),
                                                                                  components.unwrap()));
                                                        }
                                                    }
                                                    _ => {
                                                        self.tcx.sess.span_err(item.span,
                                                                               "Unknown `inspirv` \
                                                                                attribute item")
                                                    }
                                                }
                                            },
                                            _ => {
                                                    self.tcx.sess.span_err(item.span,
                                                                           "Unknown `inspirv` \
                                                                            attribute item")
                                            }
                                        }
                                    }
                                    _ => {
                                        self.tcx
                                            .sess
                                            .span_err(item.span, "Unknown `inspirv` attribute item")
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }

                if let Some(internal) = internal_type {
                    internal
                } else {
                    Type::Void // TODO: testing only
                }
            }

            ty::TyRawPtr(..) => { println!("{:?}", t.sty); unimplemented!() },

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
