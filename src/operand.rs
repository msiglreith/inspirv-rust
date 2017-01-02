
use rustc::mir;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};

use super::{BlockAndBuilder, MirContext};

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
                         -> OperandRef<'tcx>
    {
        println!("trans_operand(operand={:?})", operand);

        match *operand {
            mir::Operand::Consume(ref lvalue) => {
                // self.trans_consume(bcx, lvalue)
                unimplemented!()
            }

            mir::Operand::Constant(ref constant) => {
                /*
                let val = self.trans_constant(bcx, constant);
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
}
