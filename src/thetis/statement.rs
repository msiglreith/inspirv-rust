
use super::{MirContext, BlockAndBuilder};

use rustc::mir;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_statement(&mut self,
                           bcx: BlockAndBuilder<'bcx, 'tcx>,
                           statement: &mir::Statement<'tcx>)
                           -> BlockAndBuilder<'bcx, 'tcx> {
        debug!("trans_statement(statement={:?})", statement);
        
        match statement.kind {
            mir::StatementKind::Assign(ref lvalue, ref rvalue) => {
                if let mir::Lvalue::Local(index) = *lvalue {
                    match self.locals[index] {
                        LocalRef::Lvalue(tr_dest) => {
                            self.trans_rvalue(bcx, tr_dest, rvalue, debug_loc)
                        }
                        LocalRef::Operand(None) => {
                            let (bcx, operand) = self.trans_rvalue_operand(bcx, rvalue,
                                                                           debug_loc);
                            self.locals[index] = LocalRef::Operand(Some(operand));
                            bcx
                        }
                        LocalRef::Operand(Some(_)) => {
                            let ty = self.monomorphized_lvalue_ty(lvalue);

                            if !common::type_is_zero_size(bcx.ccx(), ty) {
                                span_bug!(statement.source_info.span,
                                          "operand {:?} already assigned",
                                          rvalue);
                            } else {
                                // If the type is zero-sized, it's already been set here,
                                // but we still need to make sure we translate the operand
                                self.trans_rvalue_operand(bcx, rvalue, debug_loc).0
                            }
                        }
                    }
                } else {
                    let tr_dest = self.trans_lvalue(&bcx, lvalue);
                    self.trans_rvalue(bcx, tr_dest, rvalue, debug_loc)
                }
            }
            mir::StatementKind::SetDiscriminant{ref lvalue, variant_index} => {
                let ty = self.monomorphized_lvalue_ty(lvalue);
                let lvalue_transed = self.trans_lvalue(&bcx, lvalue);
                bcx.with_block(|bcx|
                    adt::trans_set_discr(bcx,
                                         ty,
                                        lvalue_transed.llval,
                                        Disr::from(variant_index))
                );
                bcx
            }
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Nop => bcx,
        }
    }
}
