
use super::MirContext;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_lvalue(&mut self,
                        bcx: &BlockAndBuilder<'bcx, 'tcx>,
                        lvalue: &mir::Lvalue<'tcx>)
                        -> LvalueRef<'tcx> {
        debug!("trans_lvalue(lvalue={:?})", lvalue);

        let ccx = bcx.ccx();
        let tcx = bcx.tcx();
    }

    pub fn monomorphized_lvalue_ty(&self, lvalue: &mir::Lvalue<'tcx>) -> Ty<'tcx> {
        let tcx = self.fcx.ccx.tcx();
        let lvalue_ty = lvalue.ty(&self.mir, tcx);
        self.fcx.monomorphize(&lvalue_ty.to_ty(tcx))
    }
}
