
use rustc::mir;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};

use {BlockAndBuilder, MirContext};
use lvalue::{LvalueRef, ValueRef};

pub enum OperandValue {

}

pub struct OperandRef<'tcx> {
    // The value.
    pub val: OperandValue,

    // The type of value being returned.
    pub ty: Ty<'tcx>
}

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_operand(&mut self,
                         bcx: &BlockAndBuilder<'bcx, 'tcx>,
                         operand: &mir::Operand<'tcx>)
                         -> Option<OperandRef<'tcx>>
    {
        println!("trans_operand(operand={:?})", operand);

        match *operand {
            mir::Operand::Consume(ref lvalue) => {
                self.trans_consume(bcx, lvalue)
            }

            mir::Operand::Constant(ref constant) => {
                let val = self.trans_constant(bcx, constant);

                /*
                let operand = val.to_operand(bcx.ccx());
                if let OperandValue::Ref(ptr) = operand.val {
                    // If this is a OperandValue::Ref to an immediate constant, load it.
                    self.trans_load(bcx, ptr, operand.ty)
                } else {
                    operand
                }
                */

                unimplemented!()
            }
        }
    }

    pub fn trans_load(&mut self,
                      bcx: &BlockAndBuilder<'bcx, 'tcx>,
                      spv_val: ValueRef,
                      ty: Ty<'tcx>)
                      -> OperandRef<'tcx>
    {
        println!("trans_load: {:?} @ {:?}", spv_val, ty);
        unimplemented!()
    }

    pub fn trans_consume(&mut self,
                         bcx: &BlockAndBuilder<'bcx, 'tcx>,
                         lvalue: &mir::Lvalue<'tcx>)
                         -> Option<OperandRef<'tcx>>
    {
        println!("trans_consume(lvalue={:?})", lvalue);

        let tr_lvalue = self.trans_lvalue(bcx, lvalue);
        match tr_lvalue {
            LvalueRef::Value(val, ty) => {
                let ty = ty.to_ty(bcx.tcx());
                Some(self.trans_load(bcx, val, ty))
            }
            LvalueRef::Ref { .. } => unimplemented!(),
            LvalueRef::SigStruct(_, _) => unimplemented!(),
            LvalueRef::Ignore => None,
        }
    }

    pub fn store_operand(&mut self,
                         bcx: &BlockAndBuilder<'bcx, 'tcx>,
                         dest: LvalueRef,
                         operand: OperandRef<'tcx>)
    {
    }
}
