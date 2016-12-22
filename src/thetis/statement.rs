
use super::{MirContext, BlockAndBuilder};

use rustc::mir;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_statement(&mut self,
                           bcx: BlockAndBuilder<'bcx, 'tcx>,
                           statement: &mir::Statement<'tcx>)
                           -> BlockAndBuilder<'bcx, 'tcx> {
        debug!("trans_statement(statement={:?})", statement);
        
        match statement.kind {
            _ => bcx,
        }
    }
}
