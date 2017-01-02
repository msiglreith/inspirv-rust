
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
        self.trans_terminator(terminator);

        bcx.with_block(|block| {
            self.fcx.spv_fn_decl.borrow_mut().add_block(block.spv_block.clone()); // again.. clones!?..
        })
    }

    pub fn trans_terminator(&mut self, terminator: &mir::Terminator<'tcx>) {
        println!("trans_block: terminator: {:?}", terminator);

        match terminator.kind {
            mir::TerminatorKind::Return => {
                // self.block.branch_instr = Some(BranchInstruction::Return(OpReturn));
            }
            _ => unimplemented!(),
        }
    }

    fn bcx(&self, bb: mir::BasicBlock) -> BlockAndBuilder<'bcx, 'tcx> {
        self.blocks[bb].build()
    }
}
