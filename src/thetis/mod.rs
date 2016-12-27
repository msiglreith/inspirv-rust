
use arena::TypedArena;
use rustc_borrowck as borrowck;
use rustc::hir;
use rustc::hir::map as hir_map;
use rustc::hir::def::ExportMap;
use rustc::mir;
use rustc::mir::Mir;
use rustc::mir::traversal;
use rustc::middle::cstore::LinkMeta;
use rustc::ty::subst::Substs;
use rustc::ty::TypeFoldable;
use rustc::traits::{self, SelectionContext, Reveal};
use rustc::util::common::MemoizationMap;
use rustc_trans::util::nodemap::{FxHashMap, FxHashSet, DefIdMap};
use rustc::dep_graph::{DepGraph, DepNode, DepTrackingMap, DepTrackingMapConfig,
                       WorkProduct};
use rustc::infer::TransNormalize;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use rustc::ty::adjustment::CustomCoerceUnsized;
use rustc_incremental::IncrementalHashesMap;
use rustc::session::Session;
use rustc::session::config::{self, NoDebugInfo};
use rustc::util::common::time;
use rustc_trans::back::link;
use rustc_data_structures::indexed_vec::IndexVec;
use rustc_mir;
use rustc_passes::{mir_stats};
use rustc_trans::util::nodemap::NodeSet;
use rustc_const_eval::ConstEvalErr;
use syntax_pos::{Span};
use syntax_pos::{DUMMY_SP, NO_EXPANSION, COMMAND_LINE_EXPN, BytePos};
use syntax::attr;
use syntax::ast::{self, NodeId};

use inspirv::types::Id;
use inspirv_builder::module::{Type};

use self::monomorphize::Instance;
use self::trans_item::TransItem;
use self::context::{CrateContext, SharedCrateContext};

use std::cell::Ref;
use std::rc::Rc;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::path::Path;
use std::iter;

// A lot of the code here is ported from the rustc LLVM translator

struct Local {
    pub id: Id,
    pub ty: Type,
}

enum LocalRef {
    Local(Local),
    Ref {
        local: Local,
        referent: Option<Id>,
    },
    Interface(Vec<Local>),
}

/// Function context is the glue between MIR and functions of the SPIR-V builder.
pub struct FunctionContext<'a, 'tcx: 'a> {
    // The MIR for this function.
    pub mir: Option<Ref<'tcx, Mir<'tcx>>>,

    // If this function is being monomorphized, this contains the type
    // substitutions used.
    pub param_substs: &'tcx Substs<'tcx>,

    // The source span and nesting context where this function comes from, for
    // error reporting and symbol generation.
    pub span: Option<Span>,

    // The arena that blocks are allocated from.
    pub block_arena: &'a TypedArena<BlockS<'a, 'tcx>>,

    // This function's enclosing crate context.
    pub ccx: &'a CrateContext<'a, 'tcx>,
}

impl<'a, 'tcx> FunctionContext<'a, 'tcx> {
    /// Create a function context for the given function.
    pub fn new(ccx: &'a CrateContext<'a, 'tcx>,
               definition: Option<Instance<'tcx>>,
               block_arena: &'a TypedArena<BlockS<'a, 'tcx>>)
               -> FunctionContext<'a, 'tcx> {
        let (param_substs, def_id) = match definition {
            Some(instance) => {
                validate_substs(instance.substs);
                (instance.substs, Some(instance.def))
            }
            None => (ccx.tcx().intern_substs(&[]), None)
        };

        let mir = def_id.map(|id| ccx.tcx().item_mir(id));

        FunctionContext {
            mir: mir,
            param_substs: param_substs,
            span: None,
            block_arena: block_arena,
            ccx: ccx,
        }
    }

    pub fn mir(&self) -> Ref<'tcx, Mir<'tcx>> {
        self.mir.as_ref().map(Ref::clone).expect("fcx.mir was empty")
    }

    pub fn new_block(&'a self) -> Block<'a, 'tcx> {
        BlockS::new(self)
    }

    pub fn monomorphize<T>(&self, value: &T) -> T
        where T: TransNormalize<'tcx>
    {
        monomorphize::apply_param_substs(self.ccx.shared(),
                                         self.param_substs,
                                         value)
    }
}

/// Main context for translating MIR to SPIR-V.
pub struct MirContext<'bcx, 'tcx: 'bcx> {
    mir: Ref<'tcx, mir::Mir<'tcx>>,

    /// Function context
    fcx: &'bcx FunctionContext<'bcx, 'tcx>,

    /// A `Block` for each MIR `BasicBlock`
    blocks: IndexVec<mir::BasicBlock, Block<'bcx, 'tcx>>,

    /// The location where each MIR arg/var/tmp/ret is stored.
    locals: IndexVec<mir::Local, Option<LocalRef>>,
}

// Basic block context.  We create a block context for each basic block
// (single-entry, single-exit sequence of instructions) we generate from Rust
// code.  Each basic block we generate is attached to a function, typically
// with many basic blocks per function.  All the basic blocks attached to a
// function are organized as a directed graph.
pub struct BlockS<'blk, 'tcx: 'blk> {
    // The function context for the function to which this block is
    // attached.
    pub fcx: &'blk FunctionContext<'blk, 'tcx>,
}

impl<'blk, 'tcx> BlockS<'blk, 'tcx> {
    pub fn new(fcx: &'blk FunctionContext<'blk, 'tcx>)
               -> Block<'blk, 'tcx> {
        fcx.block_arena.alloc(BlockS {
            fcx: fcx
        })
    }

    pub fn ccx(&self) -> &'blk CrateContext<'blk, 'tcx> {
        self.fcx.ccx
    }
    pub fn fcx(&self) -> &'blk FunctionContext<'blk, 'tcx> {
        self.fcx
    }
    pub fn tcx(&self) -> TyCtxt<'blk, 'tcx, 'tcx> {
        self.fcx.ccx.tcx()
    }
    pub fn sess(&self) -> &'blk Session { self.fcx.ccx.sess() }

    pub fn mir(&self) -> Ref<'tcx, Mir<'tcx>> {
        self.fcx.mir()
    }

    pub fn monomorphize<T>(&self, value: &T) -> T
        where T: TransNormalize<'tcx>
    {
        monomorphize::apply_param_substs(self.fcx.ccx.shared(),
                                         self.fcx.param_substs,
                                         value)
    }

    pub fn build(&'blk self) -> BlockAndBuilder<'blk, 'tcx> {
        // BlockAndBuilder::new(self, OwnedBuilder::new_with_ccx(self.ccx()))
        BlockAndBuilder { bcx: self }
    }
}

pub type Block<'blk, 'tcx> = &'blk BlockS<'blk, 'tcx>;

pub struct BlockAndBuilder<'blk, 'tcx: 'blk> {
    bcx: Block<'blk, 'tcx>,
}

impl<'blk, 'tcx> BlockAndBuilder<'blk, 'tcx> {
    pub fn ccx(&self) -> &'blk CrateContext<'blk, 'tcx> {
        self.bcx.ccx()
    }
    pub fn fcx(&self) -> &'blk FunctionContext<'blk, 'tcx> {
        self.bcx.fcx()
    }
    pub fn tcx(&self) -> TyCtxt<'blk, 'tcx, 'tcx> {
        self.bcx.tcx()
    }
    pub fn sess(&self) -> &'blk Session {
        self.bcx.sess()
    }
    pub fn mir(&self) -> Ref<'tcx, Mir<'tcx>> {
        self.bcx.mir()
    }

    pub fn monomorphize<T>(&self, value: &T) -> T
        where T: TransNormalize<'tcx>
    {
        self.bcx.monomorphize(value)
    }

    pub fn with_block<F, R>(&self, f: F) -> R
        where F: FnOnce(Block<'blk, 'tcx>) -> R
    {
        let result = f(self.bcx);
        result
    }
}

pub fn trans_function<'blk, 'tcx: 'blk>(fcx: &'blk FunctionContext<'blk, 'tcx>) {
    let mir = fcx.mir();

    // Allocate a `Block` for every basic block
    let block_bcxs: IndexVec<mir::BasicBlock, Block<'blk,'tcx>> =
        mir.basic_blocks().indices().map(|_| fcx.new_block()).collect();

    let mut mircx = MirContext {
        mir: Ref::clone(&mir),
        fcx: fcx,
        blocks: block_bcxs,
        locals: IndexVec::new(),
    };

    mircx.locals = {
        let args = arg_local_refs(&fcx, &mir);

        let vars_and_temps = mir.vars_and_temps_iter().map(|local| {
            let decl = &mir.local_decls[local];
            let ty = fcx.monomorphize(&decl.ty);

            if let Some(name) = decl.name {
                // User variable
                println!("alloc: {:?} ({}) -> lvalue", local, name);
            } else {
                // Temporary
                println!("alloc: {:?} -> lvalue", local);
            }

            unimplemented!()
        });

        /*
        let mut allocate_local = |local| {
            let decl = &mir.local_decls[local];
            let ty = fcx.monomorphize(&decl.ty);

            if let Some(name) = decl.name {
                // User variable
                debug!("alloc: {:?} ({}) -> lvalue", local, name);
                LocalRef::Lvalue(lvalue)
            } else {
                // Temporary or return pointer
                if local == mir::RETURN_POINTER {
                    debug!("alloc: {:?} (return pointer) -> lvalue", local);
                    LocalRef::Lvalue(LvalueRef::new_sized(llretptr, LvalueTy::from_ty(ty)))
                } else {
                    debug!("alloc: {:?} -> lvalue", local);
                    LocalRef::Lvalue(LvalueRef::alloca(&bcx, ty, &format!("{:?}", local)))
                }
            }
        };
        */

        let ret = {
            let decl = &mir.local_decls[mir::RETURN_POINTER];
            let ty = fcx.monomorphize(&decl.ty);

            debug!("alloc: {:?} (return pointer) -> lvalue", mir::RETURN_POINTER);
            unimplemented!()
        };

        iter::once(ret)
            .chain(args.into_iter())
            .chain(vars_and_temps)
            .collect()
    };

    let mut rpo = traversal::reverse_postorder(&mir);

    // Translate the body of each block using reverse postorder
    for (bb, _) in rpo {
        mircx.trans_block(bb);
    }
}

fn arg_local_refs<'bcx, 'tcx>(fcx: &FunctionContext<'bcx, 'tcx>,
                              mir: &mir::Mir<'tcx>)
                              -> Vec<Option<LocalRef>> {
    let tcx = fcx.ccx.tcx();
    let mut idx = 0;

    /*
    let mut llarg_idx = fcx.fn_ty.ret.is_indirect() as usize;

    mir.args_iter().enumerate().map(|(arg_index, local)| {
        let arg_decl = &mir.local_decls[local];
        let arg_ty = bcx.monomorphize(&arg_decl.ty);

        if Some(local) == mir.spread_arg {
            // This argument (e.g. the last argument in the "rust-call" ABI)
            // is a tuple that was spread at the ABI level and now we have
            // to reconstruct it into a tuple local variable, from multiple
            // individual LLVM function arguments.

            let tupled_arg_tys = match arg_ty.sty {
                ty::TyTuple(ref tys) => tys,
                _ => bug!("spread argument isn't a tuple?!")
            };

            let lltemp = bcx.with_block(|bcx| {
                base::alloc_ty(bcx, arg_ty, &format!("arg{}", arg_index))
            });
            for (i, &tupled_arg_ty) in tupled_arg_tys.iter().enumerate() {
                let dst = bcx.struct_gep(lltemp, i);
                let arg = &fcx.fn_ty.args[idx];
                idx += 1;
                if common::type_is_fat_ptr(tcx, tupled_arg_ty) {
                    // We pass fat pointers as two words, but inside the tuple
                    // they are the two sub-fields of a single aggregate field.
                    let meta = &fcx.fn_ty.args[idx];
                    idx += 1;
                    arg.store_fn_arg(bcx, &mut llarg_idx,
                                     base::get_dataptr_builder(bcx, dst));
                    meta.store_fn_arg(bcx, &mut llarg_idx,
                                      base::get_meta_builder(bcx, dst));
                } else {
                    arg.store_fn_arg(bcx, &mut llarg_idx, dst);
                }
            }

            // Now that we have one alloca that contains the aggregate value,
            // we can create one debuginfo entry for the argument.
            bcx.with_block(|bcx| arg_scope.map(|scope| {
                let variable_access = VariableAccess::DirectVariable {
                    alloca: lltemp
                };
                declare_local(bcx, arg_decl.name.unwrap_or(keywords::Invalid.name()),
                              arg_ty, scope, variable_access,
                              VariableKind::ArgumentVariable(arg_index + 1),
                              bcx.fcx().span.unwrap_or(DUMMY_SP));
            }));

            return LocalRef::Lvalue(LvalueRef::new_sized(lltemp, LvalueTy::from_ty(arg_ty)));
        }

        let arg = &fcx.fn_ty.args[idx];
        idx += 1;
        let llval = if arg.is_indirect() && bcx.sess().opts.debuginfo != FullDebugInfo {
            // Don't copy an indirect argument to an alloca, the caller
            // already put it in a temporary alloca and gave it up, unless
            // we emit extra-debug-info, which requires local allocas :(.
            // FIXME: lifetimes
            if arg.pad.is_some() {
                llarg_idx += 1;
            }
            let llarg = llvm::get_param(fcx.llfn, llarg_idx as c_uint);
            llarg_idx += 1;
            llarg
        } else if !lvalue_locals.contains(local.index()) &&
                  !arg.is_indirect() && arg.cast.is_none() &&
                  arg_scope.is_none() {
            if arg.is_ignore() {
                return LocalRef::new_operand(bcx.ccx(), arg_ty);
            }

            // We don't have to cast or keep the argument in the alloca.
            // FIXME(eddyb): We should figure out how to use llvm.dbg.value instead
            // of putting everything in allocas just so we can use llvm.dbg.declare.
            if arg.pad.is_some() {
                llarg_idx += 1;
            }
            let llarg = llvm::get_param(fcx.llfn, llarg_idx as c_uint);
            llarg_idx += 1;
            let val = if common::type_is_fat_ptr(tcx, arg_ty) {
                let meta = &fcx.fn_ty.args[idx];
                idx += 1;
                assert_eq!((meta.cast, meta.pad), (None, None));
                let llmeta = llvm::get_param(fcx.llfn, llarg_idx as c_uint);
                llarg_idx += 1;
                OperandValue::Pair(llarg, llmeta)
            } else {
                OperandValue::Immediate(llarg)
            };
            let operand = OperandRef {
                val: val,
                ty: arg_ty
            };
            return LocalRef::Operand(Some(operand.unpack_if_pair(bcx)));
        } else {
            let lltemp = bcx.with_block(|bcx| {
                base::alloc_ty(bcx, arg_ty, &format!("arg{}", arg_index))
            });
            if common::type_is_fat_ptr(tcx, arg_ty) {
                // we pass fat pointers as two words, but we want to
                // represent them internally as a pointer to two words,
                // so make an alloca to store them in.
                let meta = &fcx.fn_ty.args[idx];
                idx += 1;
                arg.store_fn_arg(bcx, &mut llarg_idx,
                                 base::get_dataptr_builder(bcx, lltemp));
                meta.store_fn_arg(bcx, &mut llarg_idx,
                                  base::get_meta_builder(bcx, lltemp));
            } else  {
                // otherwise, arg is passed by value, so make a
                // temporary and store it there
                arg.store_fn_arg(bcx, &mut llarg_idx, lltemp);
            }
            lltemp
        };
        bcx.with_block(|bcx| arg_scope.map(|scope| {
            // Is this a regular argument?
            if arg_index > 0 || mir.upvar_decls.is_empty() {
                declare_local(bcx, arg_decl.name.unwrap_or(keywords::Invalid.name()), arg_ty,
                              scope, VariableAccess::DirectVariable { alloca: llval },
                              VariableKind::ArgumentVariable(arg_index + 1),
                              bcx.fcx().span.unwrap_or(DUMMY_SP));
                return;
            }

            // Or is it the closure environment?
            let (closure_ty, env_ref) = if let ty::TyRef(_, mt) = arg_ty.sty {
                (mt.ty, true)
            } else {
                (arg_ty, false)
            };
            let upvar_tys = if let ty::TyClosure(def_id, substs) = closure_ty.sty {
                substs.upvar_tys(def_id, tcx)
            } else {
                bug!("upvar_decls with non-closure arg0 type `{}`", closure_ty);
            };

            // Store the pointer to closure data in an alloca for debuginfo
            // because that's what the llvm.dbg.declare intrinsic expects.

            // FIXME(eddyb) this shouldn't be necessary but SROA seems to
            // mishandle DW_OP_plus not preceded by DW_OP_deref, i.e. it
            // doesn't actually strip the offset when splitting the closure
            // environment into its components so it ends up out of bounds.
            let env_ptr = if !env_ref {
                use base::*;
                use build::*;
                use common::*;
                let alloc = alloca(bcx, val_ty(llval), "__debuginfo_env_ptr");
                Store(bcx, llval, alloc);
                alloc
            } else {
                llval
            };

            let llclosurety = type_of::type_of(bcx.ccx(), closure_ty);
            for (i, (decl, ty)) in mir.upvar_decls.iter().zip(upvar_tys).enumerate() {
                let byte_offset_of_var_in_env =
                    machine::llelement_offset(bcx.ccx(), llclosurety, i);

                let ops = unsafe {
                    [llvm::LLVMRustDIBuilderCreateOpDeref(),
                     llvm::LLVMRustDIBuilderCreateOpPlus(),
                     byte_offset_of_var_in_env as i64,
                     llvm::LLVMRustDIBuilderCreateOpDeref()]
                };

                // The environment and the capture can each be indirect.

                // FIXME(eddyb) see above why we have to keep
                // a pointer in an alloca for debuginfo atm.
                let mut ops = if env_ref || true { &ops[..] } else { &ops[1..] };

                let ty = if let (true, &ty::TyRef(_, mt)) = (decl.by_ref, &ty.sty) {
                    mt.ty
                } else {
                    ops = &ops[..ops.len() - 1];
                    ty
                };

                let variable_access = VariableAccess::IndirectVariable {
                    alloca: env_ptr,
                    address_operations: &ops
                };
                declare_local(bcx, decl.debug_name, ty, scope, variable_access,
                              VariableKind::CapturedVariable,
                              bcx.fcx().span.unwrap_or(DUMMY_SP));
            }
        }));
        LocalRef::Lvalue(LvalueRef::new_sized(llval, LvalueTy::from_ty(arg_ty)))
    }).collect()

    */

    Vec::new()
}

pub fn trans_static(ccx: &CrateContext,
                    m: hir::Mutability,
                    id: ast::NodeId,
                    attrs: &[ast::Attribute])
                    -> Result<(), ConstEvalErr> {
    /*
    unsafe {
        let _icx = push_ctxt("trans_static");
        let def_id = ccx.tcx().map.local_def_id(id);
        let g = get_static(ccx, def_id);

        let v = ::mir::trans_static_initializer(ccx, def_id)?;

        // boolean SSA values are i1, but they have to be stored in i8 slots,
        // otherwise some LLVM optimization passes don't work as expected
        let mut val_llty = val_ty(v);
        let v = if val_llty == Type::i1(ccx) {
            val_llty = Type::i8(ccx);
            llvm::LLVMConstZExt(v, val_llty.to_ref())
        } else {
            v
        };

        let ty = ccx.tcx().item_type(def_id);
        let llty = type_of::type_of(ccx, ty);
        let g = if val_llty == llty {
            g
        } else {
            // If we created the global with the wrong type,
            // correct the type.
            let empty_string = CString::new("").unwrap();
            let name_str_ref = CStr::from_ptr(llvm::LLVMGetValueName(g));
            let name_string = CString::new(name_str_ref.to_bytes()).unwrap();
            llvm::LLVMSetValueName(g, empty_string.as_ptr());
            let new_g = llvm::LLVMRustGetOrInsertGlobal(
                ccx.llmod(), name_string.as_ptr(), val_llty.to_ref());
            // To avoid breaking any invariants, we leave around the old
            // global for the moment; we'll replace all references to it
            // with the new global later. (See base::trans_crate.)
            ccx.statics_to_rauw().borrow_mut().push((g, new_g));
            new_g
        };
        llvm::LLVMSetAlignment(g, type_of::align_of(ccx, ty));
        llvm::LLVMSetInitializer(g, v);

        // As an optimization, all shared statics which do not have interior
        // mutability are placed into read-only memory.
        if m != hir::MutMutable {
            let tcontents = ty.type_contents(ccx.tcx());
            if !tcontents.interior_unsafe() {
                llvm::LLVMSetGlobalConstant(g, llvm::True);
            }
        }

        debuginfo::create_global_var_metadata(ccx, id, g);

        if attr::contains_name(attrs,
                               "thread_local") {
            llvm::set_thread_local(g, true);
        }

        base::set_link_section(ccx, g, attrs);

        Ok(g)
    }
    */
    unimplemented!()
}


pub fn translate_to_spirv<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                    analysis: ty::CrateAnalysis,
                                    incremental_hashes_map: &IncrementalHashesMap,
                                    out_dir: &Option<&'a Path>) {
    let time_passes = tcx.sess.time_passes();

    if tcx.sess.opts.debugging_opts.mir_stats {
        mir_stats::print_mir_stats(tcx, "PRE OPTIMISATION MIR STATS");
    }

    // Run the passes that transform the MIR into a more suitable form for translation to LLVM
    // code.
    time(time_passes, "MIR optimisations", || {
        let mut passes = mir::transform::Passes::new();
        passes.push_hook(box rustc_mir::transform::dump_mir::DumpMir);
        passes.push_pass(box rustc_mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box rustc_mir::transform::simplify::SimplifyCfg::new("no-landing-pads"));

        // From here on out, regions are gone.
        passes.push_pass(box rustc_mir::transform::erase_regions::EraseRegions);

        passes.push_pass(box rustc_mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box borrowck::ElaborateDrops);
        passes.push_pass(box rustc_mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box rustc_mir::transform::simplify::SimplifyCfg::new("elaborate-drops"));

        // No lifetime analysis based on borrowing can be done from here on out.
        passes.push_pass(box rustc_mir::transform::instcombine::InstCombine::new());
        passes.push_pass(box rustc_mir::transform::deaggregator::Deaggregator);
        passes.push_pass(box rustc_mir::transform::copy_prop::CopyPropagation);

        passes.push_pass(box rustc_mir::transform::simplify::SimplifyLocals);
        passes.push_pass(box rustc_mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box rustc_mir::transform::dump_mir::Marker("PreTrans"));

        passes.run_passes(tcx);
    });

    if tcx.sess.opts.debugging_opts.mir_stats {
        mir_stats::print_mir_stats(tcx, "POST OPTIMISATION MIR STATS");
    }

    time(time_passes,
         "translation",
         move || trans_crate(tcx, analysis, &incremental_hashes_map, out_dir))
}

/// The context provided lists a set of reachable ids as calculated by
/// middle::reachable, but this contains far more ids and symbols than we're
/// actually exposing from the object file. This function will filter the set in
/// the context to the set of ids which correspond to symbols that are exposed
/// from the object file being generated.
///
/// This list is later used by linkers to determine the set of symbols needed to
/// be exposed from a dynamic library and it's also encoded into the metadata.
pub fn find_exported_symbols(tcx: TyCtxt, reachable: NodeSet) -> NodeSet {
    reachable.into_iter().filter(|&id| {
        // Next, we want to ignore some FFI functions that are not exposed from
        // this crate. Reachable FFI functions can be lumped into two
        // categories:
        //
        // 1. Those that are included statically via a static library
        // 2. Those included otherwise (e.g. dynamically or via a framework)
        //
        // Although our LLVM module is not literally emitting code for the
        // statically included symbols, it's an export of our library which
        // needs to be passed on to the linker and encoded in the metadata.
        //
        // As a result, if this id is an FFI item (foreign item) then we only
        // let it through if it's included statically.
        match tcx.map.get(id) {
            hir_map::NodeForeignItem(..) => {
                let def_id = tcx.map.local_def_id(id);
                tcx.sess.cstore.is_statically_included_foreign_item(def_id)
            }

            // Only consider nodes that actually have exported symbols.
            hir_map::NodeItem(&hir::Item {
                node: hir::ItemStatic(..), .. }) |
            hir_map::NodeItem(&hir::Item {
                node: hir::ItemFn(..), .. }) |
            hir_map::NodeImplItem(&hir::ImplItem {
                node: hir::ImplItemKind::Method(..), .. }) => {
                let def_id = tcx.map.local_def_id(id);
                let generics = tcx.item_generics(def_id);
                let attributes = tcx.get_attrs(def_id);
                (generics.parent_types == 0 && generics.types.is_empty()) &&
                // Functions marked with #[inline] are only ever translated
                // with "internal" linkage and are never exported.
                !attr::requests_inline(&attributes[..])
            }

            _ => false
        }
    }).collect()
}

fn write_metadata(cx: &SharedCrateContext,
                  exported_symbols: &NodeSet) -> Vec<u8> {
    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    enum MetadataKind {
        None,
        Uncompressed,
        Compressed
    }

    let kind = cx.sess().crate_types.borrow().iter().map(|ty| {
        match *ty {
            config::CrateTypeExecutable |
            config::CrateTypeStaticlib |
            config::CrateTypeCdylib => MetadataKind::None,

            config::CrateTypeRlib |
            config::CrateTypeMetadata => MetadataKind::Uncompressed,

            config::CrateTypeDylib |
            config::CrateTypeProcMacro => MetadataKind::Compressed,
        }
    }).max().unwrap();

    if kind == MetadataKind::None {
        return Vec::new();
    }

    let cstore = &cx.tcx().sess.cstore;
    let metadata = cstore.encode_metadata(cx.tcx(),
                                          cx.export_map(),
                                          cx.link_meta(),
                                          exported_symbols);
    if kind == MetadataKind::Uncompressed {
        return metadata;
    }

    assert!(kind == MetadataKind::Compressed);
    // TODO: ?
    return metadata;
}

fn trans_crate<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                         analysis: ty::CrateAnalysis,
                         incremental_hashes_map: &IncrementalHashesMap,
                         out_dir: &Option<&'a Path>)
{
    let _task = tcx.dep_graph.in_task(DepNode::TransCrate);

    let ty::CrateAnalysis { export_map, reachable, name, .. } = analysis;

    let exported_symbols = find_exported_symbols(tcx, reachable);
    let link_meta = link::build_link_meta(incremental_hashes_map, &name);

    let shared_ccx = SharedCrateContext::new(tcx,
                                             export_map,
                                             exported_symbols,
                                             link_meta.clone());

    // Translate the metadata.
    let metadata = time(tcx.sess.time_passes(), "write metadata", || {
        write_metadata(&shared_ccx, shared_ccx.exported_symbols())
    });

    // Run the translation item collector
    let translation_items = collect_translation_items(&shared_ccx);

    let ccx = CrateContext::new(&shared_ccx);

    for item in &translation_items {
        item.predefine(&ccx);
    }

    // translate MIR
    for item in translation_items {
        println!("{:?}", item.to_string(tcx));
        item.define(&ccx);
    }
}

fn collect_translation_items<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>)
                                                     -> FxHashSet<TransItem<'tcx>> {
    let time_passes = scx.sess().time_passes();

    let (items, inlining_map) =
        time(time_passes, "translation item collection", || {
            collector::collect_crate_translation_items(&scx)
    });

    items
}

pub fn custom_coerce_unsize_info<'scx, 'tcx>(scx: &SharedCrateContext<'scx, 'tcx>,
                                             source_ty: Ty<'tcx>,
                                             target_ty: Ty<'tcx>)
                                             -> CustomCoerceUnsized {
    let trait_ref = ty::Binder(ty::TraitRef {
        def_id: scx.tcx().lang_items.coerce_unsized_trait().unwrap(),
        substs: scx.tcx().mk_substs_trait(source_ty, &[target_ty])
    });

    match fulfill_obligation(scx, DUMMY_SP, trait_ref) {
        traits::VtableImpl(traits::VtableImplData { impl_def_id, .. }) => {
            scx.tcx().custom_coerce_unsized_kind(impl_def_id)
        }
        vtable => {
            bug!("invalid CoerceUnsized vtable: {:?}", vtable);
        }
    }
}

/// Attempts to resolve an obligation. The result is a shallow vtable resolution -- meaning that we
/// do not (necessarily) resolve all nested obligations on the impl. Note that type check should
/// guarantee to us that all nested obligations *could be* resolved if we wanted to.
pub fn fulfill_obligation<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                    span: Span,
                                    trait_ref: ty::PolyTraitRef<'tcx>)
                                    -> traits::Vtable<'tcx, ()>
{
    let tcx = scx.tcx();

    // Remove any references to regions; this helps improve caching.
    let trait_ref = tcx.erase_regions(&trait_ref);

    scx.trait_cache().memoize(trait_ref, || {
        debug!("trans::fulfill_obligation(trait_ref={:?}, def_id={:?})",
               trait_ref, trait_ref.def_id());

        // Do the initial selection for the obligation. This yields the
        // shallow result we are looking for -- that is, what specific impl.
        tcx.infer_ctxt(None, None, Reveal::All).enter(|infcx| {
            let mut selcx = SelectionContext::new(&infcx);

            let obligation_cause = traits::ObligationCause::misc(span,
                                                             ast::DUMMY_NODE_ID);
            let obligation = traits::Obligation::new(obligation_cause,
                                                     trait_ref.to_poly_trait_predicate());

            let selection = match selcx.select(&obligation) {
                Ok(Some(selection)) => selection,
                Ok(None) => {
                    // Ambiguity can happen when monomorphizing during trans
                    // expands to some humongo type that never occurred
                    // statically -- this humongo type can then overflow,
                    // leading to an ambiguous result. So report this as an
                    // overflow bug, since I believe this is the only case
                    // where ambiguity can result.
                    debug!("Encountered ambiguity selecting `{:?}` during trans, \
                            presuming due to overflow",
                           trait_ref);
                    tcx.sess.span_fatal(span,
                        "reached the recursion limit during monomorphization \
                         (selection ambiguity)");
                }
                Err(e) => {
                    span_bug!(span, "Encountered error `{:?}` selecting `{:?}` during trans",
                              e, trait_ref)
                }
            };

            debug!("fulfill_obligation: selection={:?}", selection);

            // Currently, we use a fulfillment context to completely resolve
            // all nested obligations. This is because they can inform the
            // inference of the impl's type parameters.
            let mut fulfill_cx = traits::FulfillmentContext::new();
            let vtable = selection.map(|predicate| {
                debug!("fulfill_obligation: register_predicate_obligation {:?}", predicate);
                fulfill_cx.register_predicate_obligation(&infcx, predicate);
            });
            let vtable = infcx.drain_fulfillment_cx_or_panic(span, &mut fulfill_cx, &vtable);

            info!("Cache miss: {:?} => {:?}", trait_ref, vtable);
            vtable
        })
    })
}

pub fn validate_substs(substs: &Substs) {
    assert!(!substs.needs_infer());
}

mod adt;
mod attributes;
mod block;
mod collector;
mod constants;
mod context;
mod error;
mod intrinsic;
mod lvalue;
mod monomorphize;
mod operand;
mod rvalue;
mod statement;
mod terminator;
mod trans_item;
mod type_of;
