
use super::{MirContext, BlockAndBuilder};

use rustc::mir;

use std::cell::Ref as CellRef;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_block(&mut self, bb: mir::BasicBlock) {
        let mut bcx = self.bcx(bb);
        let data = &CellRef::clone(&self.mir)[bb];

        println!("trans_block({:?}={:?})", bb, data);

        for statement in &data.statements {
            bcx = self.trans_statement(bcx, statement);
        }

        let terminator = data.terminator();
        println!("trans_block: terminator: {:?}", terminator);

        self.trans_terminator();
    }

    fn bcx(&self, bb: mir::BasicBlock) -> BlockAndBuilder<'bcx, 'tcx> {
        self.blocks[bb].build()
    }
}
