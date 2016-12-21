
use rustc::mir;
use rustc::mir::Mir;
use rustc::ty::subst::Substs;
use rustc::dep_graph::{DepGraph, DepNode, DepTrackingMap, DepTrackingMapConfig,
                       WorkProduct};
use rustc::infer::TransNormalize;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use syntax_pos::{Span};

use std::cell::Ref;
use std::cell::RefCell;
use std::marker::PhantomData;

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

    // This function's enclosing crate context.
    pub ccx: &'a CrateContext<'a, 'tcx>,
}

impl<'a, 'tcx> FunctionContext<'a, 'tcx> {
    pub fn mir(&self) -> Ref<'tcx, Mir<'tcx>> {
        self.mir.as_ref().map(Ref::clone).expect("fcx.mir was empty")
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
}

pub struct SharedCrateContext<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    project_cache: RefCell<DepTrackingMap<ProjectionCache<'tcx>>>,
}

impl<'b, 'tcx> SharedCrateContext<'b, 'tcx> {
    pub fn project_cache(&self) -> &RefCell<DepTrackingMap<ProjectionCache<'tcx>>> {
        &self.project_cache
    }

    pub fn tcx<'a>(&'a self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.tcx
    }
}

pub struct CrateContext<'a, 'tcx: 'a> {
    shared: &'a SharedCrateContext<'a, 'tcx>,
}

impl<'b, 'tcx> CrateContext<'b, 'tcx> {
    pub fn shared(&self) -> &'b SharedCrateContext<'b, 'tcx> {
        self.shared
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

mod monomorphize {
    use super::*;
    use rustc::infer::TransNormalize;
    use rustc::ty::fold::{TypeFolder, TypeFoldable};
    use rustc::ty::subst::Subst;
    use rustc::util::common::MemoizationMap;

    /// Monomorphizes a type from the AST by first applying the in-scope
    /// substitutions and then normalizing any associated types.
    pub fn apply_param_substs<'a, 'tcx, T>(scx: &SharedCrateContext<'a, 'tcx>,
                                           param_substs: &Substs<'tcx>,
                                           value: &T)
                                           -> T
        where T: TransNormalize<'tcx>
    {
        let tcx = scx.tcx();
        debug!("apply_param_substs(param_substs={:?}, value={:?})", param_substs, value);
        let substituted = value.subst(tcx, param_substs);
        let substituted = scx.tcx().erase_regions(&substituted);
        AssociatedTypeNormalizer::new(scx).fold(&substituted)
    }

    struct AssociatedTypeNormalizer<'a, 'b: 'a, 'gcx: 'b> {
        shared: &'a SharedCrateContext<'b, 'gcx>,
    }

    impl<'a, 'b, 'gcx> AssociatedTypeNormalizer<'a, 'b, 'gcx> {
        fn new(shared: &'a SharedCrateContext<'b, 'gcx>) -> Self {
            AssociatedTypeNormalizer {
                shared: shared,
            }
        }

        fn fold<T:TypeFoldable<'gcx>>(&mut self, value: &T) -> T {
            if !value.has_projection_types() {
                value.clone()
            } else {
                value.fold_with(self)
            }
        }
    }

    impl<'a, 'b, 'gcx> TypeFolder<'gcx, 'gcx> for AssociatedTypeNormalizer<'a, 'b, 'gcx> {
        fn tcx<'c>(&'c self) -> TyCtxt<'c, 'gcx, 'gcx> {
            self.shared.tcx()
        }

        fn fold_ty(&mut self, ty: Ty<'gcx>) -> Ty<'gcx> {
            if !ty.has_projection_types() {
                ty
            } else {
                self.shared.project_cache().memoize(ty, || {
                    debug!("AssociatedTypeNormalizer: ty={:?}", ty);
                    self.shared.tcx().normalize_associated_type(&ty)
                })
            }
        }
    }

}
