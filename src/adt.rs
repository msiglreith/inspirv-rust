
use rustc::ty::{self, Ty, AdtKind};
use rustc_trans::Disr;

use inspirv::types::*;

use Block;

pub fn trans_set_discr<'blk, 'tcx>(bcx: Block<'blk, 'tcx>, t: Ty<'tcx>,
                                   val: Id, to: Disr) {
    // TODO
}
