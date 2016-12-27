
use rustc::mir;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};
use rustc::mir::tcx::LvalueTy;

use inspirv::types::*;
use inspirv_builder::module::{Type};

use super::{BlockAndBuilder, MirContext};

pub enum LvalueRef<'tcx> {
    Value(ValueRef<'tcx>),
    SigStruct(Vec<ValueRef<'tcx>>),
}

enum LvalueInner<'tcx> {
    LvalueRef(LvalueRef<'tcx>),
    AccessChain,
}

pub struct ValueRef<'tcx> {
    pub spvid: Id,

    pub spvty: Type,

    /// Monomorphized type of this lvalue, including variant information
    pub ty: LvalueTy<'tcx>,
}

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    fn revolve_lvalue(&mut self,
                      bcx: &BlockAndBuilder<'bcx, 'tcx>,
                      lvalue: &mir::Lvalue<'tcx>)
                      -> LvalueInner<'tcx> {
        let ccx = bcx.ccx();
        let tcx = bcx.tcx();

        let result = match *lvalue {
            mir::Lvalue::Local(index) => {
                match self.locals[index] {
                    _ => unimplemented!(),
                }
            }
            mir::Lvalue::Static(def_id) => {
                let const_ty = self.monomorphized_lvalue_ty(lvalue);
                bug!("unsupported static lvalue {:?}", const_ty)
            }
            mir::Lvalue::Projection(ref proj) => {
                unimplemented!()
            }
        };

        result
    }

    pub fn trans_lvalue(&mut self,
                        bcx: &BlockAndBuilder<'bcx, 'tcx>,
                        lvalue: &mir::Lvalue<'tcx>)
                        -> LvalueRef<'tcx> {
        println!("trans_lvalue(lvalue={:?})", lvalue);

        let inner = self.revolve_lvalue(bcx, lvalue);

        // Lift inner lvalue to an simplier type if possible

        unimplemented!()
    }

    pub fn monomorphized_lvalue_ty(&self, lvalue: &mir::Lvalue<'tcx>) -> Ty<'tcx> {
        let tcx = self.fcx.ccx.tcx();
        let lvalue_ty = lvalue.ty(&self.mir, tcx);
        self.fcx.monomorphize(&lvalue_ty.to_ty(tcx))
    }
}
