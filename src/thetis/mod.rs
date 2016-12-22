
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
use rustc::dep_graph::{DepGraph, DepNode, DepTrackingMap, DepTrackingMapConfig,
                       WorkProduct};
use rustc::infer::TransNormalize;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use rustc_incremental::IncrementalHashesMap;
use rustc::session::Session;
use rustc::session::config::{self, NoDebugInfo};
use rustc::util::common::time;
use rustc_trans::back::link;
use rustc_data_structures::indexed_vec::IndexVec;
use rustc_mir;
use rustc_passes::{mir_stats};
use rustc_trans::util::nodemap::NodeSet;
use syntax_pos::{Span};
use syntax_pos::{DUMMY_SP, NO_EXPANSION, COMMAND_LINE_EXPN, BytePos};
use syntax::attr;

use std::cell::Ref;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::path::Path;

// A lot of the code here is translated from the rustc LLVM translator

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
}

pub struct SharedCrateContext<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    export_map: ExportMap,
    exported_symbols: NodeSet,
    link_meta: LinkMeta,
    project_cache: RefCell<DepTrackingMap<ProjectionCache<'tcx>>>,
}

impl<'b, 'tcx> SharedCrateContext<'b, 'tcx> {
    pub fn new(tcx: TyCtxt<'b, 'tcx, 'tcx>,
               export_map: ExportMap,
               exported_symbols: NodeSet,
               link_meta: LinkMeta)
               -> SharedCrateContext<'b, 'tcx> {
        SharedCrateContext {
            tcx: tcx,
            export_map: export_map,
            exported_symbols: exported_symbols,
            link_meta: link_meta,
            project_cache: RefCell::new(DepTrackingMap::new(tcx.dep_graph.clone())),
        }
    }

    pub fn project_cache(&self) -> &RefCell<DepTrackingMap<ProjectionCache<'tcx>>> {
        &self.project_cache
    }

    pub fn tcx<'a>(&'a self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.tcx
    }

    pub fn export_map<'a>(&'a self) -> &'a ExportMap {
        &self.export_map
    }

    pub fn exported_symbols<'a>(&'a self) -> &'a NodeSet {
        &self.exported_symbols
    }

    pub fn sess<'a>(&'a self) -> &'a Session {
        &self.tcx.sess
    }

    pub fn link_meta<'a>(&'a self) -> &'a LinkMeta {
        &self.link_meta
    }
}

pub struct CrateContext<'a, 'tcx: 'a> {
    shared: &'a SharedCrateContext<'a, 'tcx>,
}

impl<'b, 'tcx> CrateContext<'b, 'tcx> {
    pub fn shared(&self) -> &'b SharedCrateContext<'b, 'tcx> {
        self.shared
    }

    pub fn tcx<'a>(&'a self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.shared.tcx
    }

    pub fn sess<'a>(&'a self) -> &'a Session {
        &self.shared.tcx.sess
    }
}

pub struct ProjectionCache<'gcx> {
    data: PhantomData<&'gcx ()>
}

impl<'gcx> DepTrackingMapConfig for ProjectionCache<'gcx> {
    type Key = Ty<'gcx>;
    type Value = Ty<'gcx>;
    fn to_dep_node(key: &Self::Key) -> DepNode<DefId> {
        // Ideally, we'd just put `key` into the dep-node, but we
        // can't put full types in there. So just collect up all the
        // def-ids of structs/enums as well as any traits that we
        // project out of. It doesn't matter so much what we do here,
        // except that if we are too coarse, we'll create overly
        // coarse edges between impls and the trans. For example, if
        // we just used the def-id of things we are projecting out of,
        // then the key for `<Foo as SomeTrait>::T` and `<Bar as
        // SomeTrait>::T` would both share a dep-node
        // (`TraitSelect(SomeTrait)`), and hence the impls for both
        // `Foo` and `Bar` would be considered inputs. So a change to
        // `Bar` would affect things that just normalized `Foo`.
        // Anyway, this heuristic is not ideal, but better than
        // nothing.
        let def_ids: Vec<DefId> =
            key.walk()
               .filter_map(|t| match t.sty {
                   ty::TyAdt(adt_def, _) => Some(adt_def.did),
                   ty::TyProjection(ref proj) => Some(proj.trait_ref.def_id),
                   _ => None,
               })
               .collect();
        DepNode::TraitSelect(def_ids)
    }
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
        unimplemented!()
    }
}

pub type Block<'blk, 'tcx> = &'blk BlockS<'blk, 'tcx>;

pub struct BlockAndBuilder<'blk, 'tcx: 'blk> {
    bcx: Block<'blk, 'tcx>,
}

impl<'blk, 'tcx> BlockAndBuilder<'blk, 'tcx> {
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
}

pub fn trans_mir<'blk, 'tcx: 'blk>(fcx: &'blk FunctionContext<'blk, 'tcx>) {
    let mir = fcx.mir();

    // Allocate a `Block` for every basic block
    let block_bcxs: IndexVec<mir::BasicBlock, Block<'blk,'tcx>> =
        mir.basic_blocks().indices().map(|_| fcx.new_block()).collect();

    let mut mircx = MirContext {
        mir: Ref::clone(&mir),
        fcx: fcx,
        blocks: block_bcxs,
    };

    let mut rpo = traversal::reverse_postorder(&mir);

    // Translate the body of each block using reverse postorder
    for (bb, _) in rpo {
        mircx.trans_block(bb);
    }
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
}

mod block;
mod monomorphize;
mod statement;
mod terminator;

