
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