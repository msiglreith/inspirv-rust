
use rustc::dep_graph::DepTrackingMap;
use rustc::dep_graph::DepTrackingMapConfig;
use rustc::dep_graph::DepNode;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::util::nodemap::{FxHashMap, FxHashSet, NodeSet};
use rustc::hir::def::ExportMap;
use rustc::hir::def_id::DefId;
use rustc::middle::cstore::LinkMeta;
use rustc::session::Session;
use rustc::ty::subst::Substs;
use rustc::traits;

use std::cell::RefCell;
use std::marker::PhantomData;

use inspirv::core::enumeration::*;
use inspirv_builder::function::FuncId;
use inspirv_builder::module::{ModuleBuilder};

use super::trans_item::TransItem;
use super::monomorphize::Instance;

const VERSION_INSPIRV_RUST: u32 = 0x00010000; // |major(1 byte)|minor(1 byte)|patch(2 byte)|

pub struct SharedCrateContext<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    export_map: ExportMap,
    exported_symbols: NodeSet,
    link_meta: LinkMeta,
    translation_items: RefCell<FxHashSet<TransItem<'tcx>>>,
    trait_cache: RefCell<DepTrackingMap<TraitSelectionCache<'tcx>>>,
    project_cache: RefCell<DepTrackingMap<ProjectionCache<'tcx>>>,
    builder: RefCell<ModuleBuilder>,

    /// Cache instances of monomorphic and polymorphic items
    instances: RefCell<FxHashMap<Instance<'tcx>, FuncId>>,
}

impl<'b, 'tcx> SharedCrateContext<'b, 'tcx> {
    pub fn new(tcx: TyCtxt<'b, 'tcx, 'tcx>,
               export_map: ExportMap,
               exported_symbols: NodeSet,
               link_meta: LinkMeta)
               -> SharedCrateContext<'b, 'tcx> {
        let mut builder = ModuleBuilder::new();
        builder.with_source(SourceLanguage::SourceLanguageUnknown, VERSION_INSPIRV_RUST);

        SharedCrateContext {
            tcx: tcx,
            export_map: export_map,
            exported_symbols: exported_symbols,
            link_meta: link_meta,
            translation_items: RefCell::new(FxHashSet()),
            trait_cache: RefCell::new(DepTrackingMap::new(tcx.dep_graph.clone())),
            project_cache: RefCell::new(DepTrackingMap::new(tcx.dep_graph.clone())),
            builder: RefCell::new(builder),
            instances: RefCell::new(FxHashMap()),
        }
    }

    pub fn trait_cache(&self) -> &RefCell<DepTrackingMap<TraitSelectionCache<'tcx>>> {
        &self.trait_cache
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

    pub fn spv<'a>(&'a self) -> &'a RefCell<ModuleBuilder> {
        &self.builder
    }

    pub fn link_meta<'a>(&'a self) -> &'a LinkMeta {
        &self.link_meta
    }

    pub fn translation_items(&self) -> &RefCell<FxHashSet<TransItem<'tcx>>> {
        &self.translation_items
    }

    /// Given the def-id of some item that has no type parameters, make
    /// a suitable "empty substs" for it.
    pub fn empty_substs_for_def_id(&self, item_def_id: DefId) -> &'tcx Substs<'tcx> {
        Substs::for_item(self.tcx(), item_def_id,
                         |_, _| self.tcx().mk_region(ty::ReErased),
                         |_, _| {
            bug!("empty_substs_for_def_id: {:?} has type parameters", item_def_id)
        })
    }
}

pub struct CrateContext<'a, 'tcx: 'a> {
    shared: &'a SharedCrateContext<'a, 'tcx>,
}

impl<'b, 'tcx> CrateContext<'b, 'tcx> {
    pub fn new(shared: &'b SharedCrateContext<'b, 'tcx>) -> CrateContext<'b, 'tcx> {
        CrateContext {
            shared: shared,
        }
    }

    pub fn shared(&self) -> &'b SharedCrateContext<'b, 'tcx> {
        self.shared
    }

    pub fn tcx<'a>(&'a self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.shared.tcx
    }

    pub fn sess<'a>(&'a self) -> &'a Session {
        &self.shared.tcx.sess
    }

    pub fn spv<'a>(&'a self) -> &'a RefCell<ModuleBuilder> {
        &self.shared.builder
    }

    pub fn instances<'a>(&'a self) -> &'a RefCell<FxHashMap<Instance<'tcx>, FuncId>> {
        &self.shared.instances
    }
}

// Implement DepTrackingMapConfig for `trait_cache`
pub struct TraitSelectionCache<'tcx> {
    data: PhantomData<&'tcx ()>
}

impl<'tcx> DepTrackingMapConfig for TraitSelectionCache<'tcx> {
    type Key = ty::PolyTraitRef<'tcx>;
    type Value = traits::Vtable<'tcx, ()>;
    fn to_dep_node(key: &ty::PolyTraitRef<'tcx>) -> DepNode<DefId> {
        key.to_poly_trait_predicate().dep_node()
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
