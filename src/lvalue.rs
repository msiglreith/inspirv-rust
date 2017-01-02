
use rustc::mir;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};
use rustc::mir::tcx::LvalueTy;

use inspirv::types::*;
use inspirv_builder::module::{Type};

use super::{BlockAndBuilder, MirContext, LocalRef};

pub enum LvalueRef {
    Value(ValueRef),
    Ref(ValueRef, Option<Id>),
    SigStruct(Vec<ValueRef>),
    Ignore,
}

enum LvalueInner {
    LvalueRef(LvalueRef),
    AccessChain,
}

pub struct ValueRef {
    pub spvid: Id,

    pub spvty: Type,

    // Monomorphized type of this lvalue, including variant information
    // pub ty: LvalueTy<'tcx>,
}

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    fn revolve_lvalue(&mut self,
                      bcx: &BlockAndBuilder<'bcx, 'tcx>,
                      lvalue: &mir::Lvalue<'tcx>)
                      -> LvalueInner {
        let ccx = bcx.ccx();
        let tcx = bcx.tcx();

        let result = match *lvalue {
            mir::Lvalue::Local(index) => {
                let lvalue_ref = match self.locals[index] {
                    Some(LocalRef::Local(ref local)) => {
                        LvalueRef::Value(ValueRef {
                            spvid: local.id,
                            spvty: local.ty.clone(),
                        })
                    }
                    Some(LocalRef::Ref { ref local, referent }) => {
                        LvalueRef::Ref(
                            ValueRef {
                                spvid: local.id,
                                spvty: local.ty.clone(),
                            },
                            referent
                        )
                    }
                    Some(LocalRef::Interface(ref locals)) => {
                        unimplemented!()
                    }
                    None => LvalueRef::Ignore,
                };

                LvalueInner::LvalueRef(lvalue_ref)
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
                        -> LvalueRef {
        println!("trans_lvalue(lvalue={:?})", lvalue);

        let inner = self.revolve_lvalue(bcx, lvalue);

        // Lift inner lvalue to an simplier type if possible
        match inner {
            LvalueInner::LvalueRef(lvalue) => lvalue,
            LvalueInner::AccessChain => unimplemented!()
        }
    }

    pub fn monomorphized_lvalue_ty(&self, lvalue: &mir::Lvalue<'tcx>) -> Ty<'tcx> {
        let tcx = self.fcx.ccx.tcx();
        let lvalue_ty = lvalue.ty(&self.mir, tcx);
        self.fcx.monomorphize(&lvalue_ty.to_ty(tcx))
    }
}
