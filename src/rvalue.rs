
use rustc::mir;

use super::{BlockAndBuilder, MirContext};
use super::lvalue::LvalueRef;

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_rvalue(&mut self,
                        bcx: BlockAndBuilder<'bcx, 'tcx>,
                        dest: LvalueRef,
                        rvalue: &mir::Rvalue<'tcx>)
                        -> BlockAndBuilder<'bcx, 'tcx>
    {
        println!("trans_rvalue(rvalue={:?})", rvalue);

        match *rvalue {
           mir::Rvalue::Use(ref operand) => {
               /*
               let tr_operand = self.trans_operand(&bcx, operand);
               self.store_operand(&bcx, dest.llval, tr_operand);
               */
               bcx
           }

            mir::Rvalue::Cast(mir::CastKind::Unsize, ref source, cast_ty) => {
                let cast_ty = bcx.monomorphize(&cast_ty);

                /*
                if common::type_is_fat_ptr(bcx.tcx(), cast_ty) {
                    // into-coerce of a thin pointer to a fat pointer - just
                    // use the operand path.
                    let (bcx, temp) = self.trans_rvalue_operand(bcx, rvalue, debug_loc);
                    self.store_operand(&bcx, dest.llval, temp);
                    return bcx;
                }

                // Unsize of a nontrivial struct. I would prefer for
                // this to be eliminated by MIR translation, but
                // `CoerceUnsized` can be passed by a where-clause,
                // so the (generic) MIR may not be able to expand it.
                let operand = self.trans_operand(&bcx, source);
                let operand = operand.pack_if_pair(&bcx);
                bcx.with_block(|bcx| {
                    match operand.val {
                        OperandValue::Pair(..) => bug!(),
                        OperandValue::Immediate(llval) => {
                            // unsize from an immediate structure. We don't
                            // really need a temporary alloca here, but
                            // avoiding it would require us to have
                            // `coerce_unsized_into` use extractvalue to
                            // index into the struct, and this case isn't
                            // important enough for it.
                            debug!("trans_rvalue: creating ugly alloca");
                            let lltemp = base::alloc_ty(bcx, operand.ty, "__unsize_temp");
                            base::store_ty(bcx, llval, lltemp, operand.ty);
                            base::coerce_unsized_into(bcx,
                                                      lltemp, operand.ty,
                                                      dest.llval, cast_ty);
                        }
                        OperandValue::Ref(llref) => {
                            base::coerce_unsized_into(bcx,
                                                      llref, operand.ty,
                                                      dest.llval, cast_ty);
                        }
                    }
                });
                */
                bcx
            }

            mir::Rvalue::Repeat(ref elem, ref count) => {
                /*
                let tr_elem = self.trans_operand(&bcx, elem);
                let size = count.value.as_u64(bcx.tcx().sess.target.uint_type);
                let size = C_uint(bcx.ccx(), size);
                let base = base::get_dataptr_builder(&bcx, dest.llval);
                let bcx = bcx.map_block(|block| {
                    tvec::slice_for_each(block, base, tr_elem.ty, size, |block, llslot| {
                        self.store_operand_direct(block, llslot, tr_elem);
                        block
                    })
                });
                */
                bcx
            }

            mir::Rvalue::Aggregate(ref kind, ref operands) => {
                /*
                match *kind {
                    mir::AggregateKind::Adt(adt_def, variant_index, _, active_field_index) => {
                        let disr = Disr::from(adt_def.variants[variant_index].disr_val);
                        bcx.with_block(|bcx| {
                            adt::trans_set_discr(bcx,
                                dest.ty.to_ty(bcx.tcx()), dest.llval, Disr::from(disr));
                        });
                        for (i, operand) in operands.iter().enumerate() {
                            let op = self.trans_operand(&bcx, operand);
                            // Do not generate stores and GEPis for zero-sized fields.
                            if !common::type_is_zero_size(bcx.ccx(), op.ty) {
                                let val = adt::MaybeSizedValue::sized(dest.llval);
                                let field_index = active_field_index.unwrap_or(i);
                                let lldest_i = adt::trans_field_ptr_builder(&bcx,
                                    dest.ty.to_ty(bcx.tcx()),
                                    val, disr, field_index);
                                self.store_operand(&bcx, lldest_i, op);
                            }
                        }
                    },
                    _ => {
                        for (i, operand) in operands.iter().enumerate() {
                            let op = self.trans_operand(&bcx, operand);
                            // Do not generate stores and GEPis for zero-sized fields.
                            if !common::type_is_zero_size(bcx.ccx(), op.ty) {
                                // Note: perhaps this should be StructGep, but
                                // note that in some cases the values here will
                                // not be structs but arrays.
                                let dest = bcx.gepi(dest.llval, &[0, i]);
                                self.store_operand(&bcx, dest, op);
                            }
                        }
                    }
                }
                */
                bcx
            }

            mir::Rvalue::InlineAsm { .. } |
            mir::Rvalue::Box(..) => {
                bug!("Invalid inline asm")
            }

            _ => {
                /*
                assert!(rvalue_creates_operand(&self.mir, &bcx, rvalue));
                let (bcx, temp) = self.trans_rvalue_operand(bcx, rvalue, debug_loc);
                self.store_operand(&bcx, dest.llval, temp);
                */
                bcx
            }
        }
    }
}