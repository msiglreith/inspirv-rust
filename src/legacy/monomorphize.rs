use rustc::ty::subst::{Subst, Substs};
use rustc::ty::{Ty, TyCtxt, TypeFoldable};
use rustc::infer::TransNormalize;

pub fn apply_param_substs<'a, 'tcx, T>(tcx: &TyCtxt<'a, 'tcx, 'tcx>, param_substs: &Substs<'tcx>, value: &T) -> T
    where T: TypeFoldable<'tcx> + TransNormalize<'tcx>
{
    let substituted = value.subst(*tcx, param_substs);
    tcx.normalize_associated_type(&substituted)
}

pub fn apply_ty_substs<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>, ty_substs: &Substs<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    let substituted = ty.subst(*tcx, ty_substs);
    tcx.normalize_associated_type(&substituted)
}
