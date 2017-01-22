
use super::{MirContext, BlockAndBuilder};

use rustc::mir;

use inspirv::core::instruction::*;
use inspirv::core::enumeration::*;
use inspirv::instruction::BranchInstruction;

use std::cell::Ref as CellRef;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_block(&mut self, bb: mir::BasicBlock) {
        let mut bcx = self.bcx(bb);
        let data = &CellRef::clone(&self.mir)[bb];

        println!("trans_block({:?}={:#?})", bb, data);

        for statement in &data.statements {
            bcx = self.trans_statement(bcx, statement);
        }

        let terminator = data.terminator();
        println!("trans_block: terminator: {:#?}", terminator);

        match terminator.kind {
            mir::TerminatorKind::Return => {
                bcx.with_block(|block| {
                    block.spv_block.borrow_mut().branch_instr = Some(
                        BranchInstruction::Return(OpReturn));
                });
            }

            mir::TerminatorKind::Unreachable => {
                bcx.with_block(|block| {
                    block.spv_block.borrow_mut().branch_instr = Some(
                        BranchInstruction::Unreachable(OpUnreachable));
                });
            }

            mir::TerminatorKind::Resume => {
                bcx.with_block(|block| {
                    block.spv_block.borrow_mut().branch_instr = Some(
                        BranchInstruction::Return(OpReturn));
                });
            }

            mir::TerminatorKind::Call { ref func, ref args, ref destination, .. } => {
                let callee = self.trans_operand(&bcx, func);

                // TODO:
                bcx.with_block(|block| {
                    block.spv_block.borrow_mut().branch_instr = Some(
                        BranchInstruction::Unreachable(OpUnreachable));
                });
                // unimplemented!()
            }

            mir::TerminatorKind::Drop { target, .. } |
            mir::TerminatorKind::Goto { target } |
            mir::TerminatorKind::Assert { target, .. } => {
                let target = {
                    let target_bcx = self.bcx(target);
                    bcx.with_block(|block| block.spv_block.borrow_mut().label)
                };
                bcx.with_block(|block| {
                    block.spv_block.borrow_mut().branch_instr = Some(
                        BranchInstruction::Branch(OpBranch(target)));
                });
            }

            _ => unimplemented!(),
        }

        bcx.with_block(|block| {
            self.fcx.spv_fn_decl.borrow_mut().add_block(block.spv_block.borrow().clone()); // again.. clones!?..
        })
    }

    fn bcx(&self, bb: mir::BasicBlock) -> BlockAndBuilder<'bcx, 'tcx> {
        self.blocks[bb].build()
    }
}
