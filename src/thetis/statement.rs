
use super::{MirContext, BlockAndBuilder};
use super::adt;

use rustc::mir;
use rustc_trans::Disr;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_statement(&mut self,
                           bcx: BlockAndBuilder<'bcx, 'tcx>,
                           statement: &mir::Statement<'tcx>)
                           -> BlockAndBuilder<'bcx, 'tcx> {
        println!("trans_statement(statement={:?})", statement);
        
        match statement.kind {
            mir::StatementKind::Assign(ref lvalue, ref rvalue) => {
                let tr_dest = self.trans_lvalue(&bcx, lvalue);
                self.trans_rvalue(bcx, tr_dest, rvalue)
            }
            mir::StatementKind::SetDiscriminant{ref lvalue, variant_index} => {
                /*
                let ty = self.monomorphized_lvalue_ty(lvalue);
                let lvalue_transed = self.trans_lvalue(&bcx, lvalue);
                bcx.with_block(|bcx|
                    adt::trans_set_discr(bcx,
                                         ty,
                                         lvalue_transed.spvid,
                                         Disr::from(variant_index))
                );
                */
                bcx
            }
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Nop => bcx,
        }
    }
}
