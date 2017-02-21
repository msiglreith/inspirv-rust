
use rustc::mir;

use {BlockAndBuilder, MirContext};
use lvalue::LvalueRef;
use operand::OperandValue;

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
                let tr_operand = self.trans_operand(&bcx, operand);
                if let Some(tr_operand) = tr_operand {
                    self.store_operand(&bcx, dest, tr_operand);
                }
                bcx
           }

            mir::Rvalue::Cast(mir::CastKind::Misc, ref source, cast_ty) => {
                let cast_ty = bcx.monomorphize(&cast_ty);

                // casting a constant
                // just define a new constant with cast type
                match *source {
                    mir::Operand::Constant(_) => {
                        // TODO:
                        return bcx;
                    }
                    _ => {}
                }

                let operand = self.trans_operand(&bcx, source).unwrap();
                bcx.with_block(|bcx| {
                    match operand.val {
                        OperandValue::Immediate(ref val) => {
                            println!("cast_rvalue(cast_ty={:?})", cast_ty);

                            // TODO:
                        }
                        OperandValue::Null => {
                            bug!()
                        }
                    }
                });
                bcx
            }

            mir::Rvalue::Ref(_, _, ref lvalue) => {
                let tr_lvalue = self.trans_lvalue(&bcx, lvalue);

                println!("Ref {:?}", tr_lvalue);
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

            mir::Rvalue::Box(..) => {
                bug!("Invalid box rvalue")
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