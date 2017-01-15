
use rustc::mir;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};
use rustc::mir::tcx::LvalueTy;

use inspirv::types::*;
use inspirv_builder::module::{Type};

use {BlockAndBuilder, MirContext, LocalRef};

#[derive(Debug, Clone)]
pub enum LvalueRef<'tcx> {
    Value(ValueRef, LvalueTy<'tcx>),
    Ref(ValueRef, Option<Id>, LvalueTy<'tcx>),
    SigStruct(Vec<ValueRef>, LvalueTy<'tcx>),
    Ignore,
}

#[derive(Debug, Clone)]
enum LvalueInner<'tcx> {
    LvalueRef(LvalueRef<'tcx>),
    AccessChain,
}

#[derive(Debug, Clone)]
pub struct ValueRef{
    pub spvid: Id,

    pub spvty: Type,
}

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    fn resolve_lvalue(&mut self,
                      bcx: &BlockAndBuilder<'bcx, 'tcx>,
                      lvalue: &mir::Lvalue<'tcx>)
                      -> LvalueInner<'tcx> {
        let ccx = bcx.ccx();
        let tcx = bcx.tcx();

        let result = match *lvalue {
            mir::Lvalue::Local(index) => {
                let ty = LvalueTy::from_ty(self.monomorphized_lvalue_ty(lvalue));
                let lvalue_ref = match self.locals[index] {
                    Some(LocalRef::Local(ref local)) => {
                        LvalueRef::Value(
                            ValueRef {
                                spvid: local.id,
                                spvty: local.ty.clone(),
                            },
                            ty,
                        )
                    }
                    Some(LocalRef::Ref { ref local, referent }) => {
                        LvalueRef::Ref(
                            ValueRef {
                                spvid: local.id,
                                spvty: local.ty.clone(),
                            },
                            referent,
                            ty,
                        )
                    }
                    Some(LocalRef::Interface(ref locals)) => {
                        LvalueRef::SigStruct(
                            locals.iter().map(|local| {
                                ValueRef {
                                    spvid: local.id,
                                    spvty: local.ty.clone(),
                                }
                            }).collect(),
                            ty,
                        )
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
                        -> LvalueRef<'tcx> {
        println!("trans_lvalue(lvalue={:?})", lvalue);

        let inner = self.resolve_lvalue(bcx, lvalue);

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
