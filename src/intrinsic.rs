
use rustc::mir::repr::*;
use rustc::middle::const_val::ConstVal::*;
use rustc_const_math::ConstInt;
use trans::{InspirvBlock, SpirvOperand, SpirvLvalue};
use inspirv::types::*;
use inspirv::core::instruction::*;
use inspirv_builder::module::{self, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    Swizzle {
        components_out: u32,
        components_in: u32
    },
    Shuffle {
        components_out: u32,
        components_in0: u32,
        components_in1: u32
    },
    VectorNew(Vec<u32>),
}

impl<'a, 'b, 'v: 'a, 'tcx: 'v> InspirvBlock<'a, 'b, 'v, 'tcx> {
    pub fn emit_intrinsic(&mut self, intrinsic: &Intrinsic, args: &[Operand<'tcx>]) -> Id {
        use self::Intrinsic::*;
        let args_ops = args.iter().map(|arg| self.trans_operand(arg)).collect::<Vec<_>>();
        let component_ids = args_ops.iter().filter_map(
                                |arg| match *arg {
                                    SpirvOperand::Constant(c, _) => Some(c),
                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, ref op_ty, _)) => {
                                        let op_id = self.ctxt.builder.alloc_id();
                                        let op_load = OpLoad(self.ctxt.builder.define_type(op_ty), op_id, op_ptr_id, None);
                                        self.block.emit_instruction(op_load);
                                        Some(op_id)
                                    }
                                    _ => None
                                }).collect::<Vec<_>>();

        match *intrinsic {
            VectorNew(ref components) => self.emit_intrinsic_vector_new(components, args_ops, component_ids),
            Swizzle { components_out, components_in } => self.emit_instrinsic_swizzle(
                                                                    components_in,
                                                                    components_out,
                                                                    args,
                                                                    args_ops,
                                                                    component_ids,
                                                              ),
            Shuffle { components_out:4 , components_in0: 4, components_in1: 4 } => {
                let ty = Type::Vector{ base: Box::new(Type::Float(32)), components: 4 };
                if args_ops[2..].iter().all(|arg| arg.is_constant()) {
                    // all args are constants!
                    let result_id = self.ctxt.builder.alloc_id();
                    // components
                    let comp_x = extract_u32_from_operand(&args[2]);
                    if comp_x >= 8 { bug!{"inspirv: shuffle component `x` out of range {:?}", comp_x} }
                    let comp_y = extract_u32_from_operand(&args[3]);
                    if comp_y >= 8 { bug!{"inspirv: shuffle component `y` out of range {:?}", comp_y} }
                    let comp_z = extract_u32_from_operand(&args[4]);
                    if comp_z >= 8 { bug!{"inspirv: shuffle component `z` out of range {:?}", comp_z} }
                    let comp_w = extract_u32_from_operand(&args[5]);
                    if comp_w >= 8 { bug!{"inspirv: shuffle component `w` out of range {:?}", comp_w} }
                    self.block.emit_instruction(
                        OpVectorShuffle(
                            self.ctxt.builder.define_type(&ty),
                            result_id,
                            component_ids[0],
                            component_ids[1],
                            vec![
                                LiteralInteger(comp_x),
                                LiteralInteger(comp_y),
                                LiteralInteger(comp_z),
                                LiteralInteger(comp_w),
                            ],
                        )
                    );
                    result_id
                } else {
                    panic!("Unhandled dynamic `shuffle4`")
                }
            }
            _ => bug!("Unknown function call intrinsic")
        }
    }

    

    fn emit_instrinsic_swizzle(&mut self, num_input_components: u32, num_output_components: u32, args: &[Operand<'tcx>], args_ops: Vec<SpirvOperand>, component_ids: Vec<Id>) -> Id {
        assert!(num_output_components as usize == component_ids.len());
        let ty = Type::Vector{ base: Box::new(Type::Float(32)), components: num_output_components as u32 };
        if args_ops[1..].iter().all(|arg| arg.is_constant()) {
            // all args are constants!
            let result_id = self.ctxt.builder.alloc_id();
            // components
            let components = (0..num_output_components as usize).map(|i| {
                let component = extract_u32_from_operand(&args[i+1]);
                if component >= num_input_components as u32 {
                    bug!{"inspirv: swizzle component({:?}) out of range {:?}", i, component}
                }
                LiteralInteger(component)
            }).collect::<Vec<_>>();
            self.block.emit_instruction(
                OpVectorShuffle(
                    self.ctxt.builder.define_type(&ty),
                    result_id,
                    component_ids[0],
                    component_ids[0],
                    components
                )
            );
            result_id
        } else {
            panic!("Unhandled dynamic swizzle!")
        }
    }

    fn emit_intrinsic_vector_new(&mut self, num_components: &[u32], args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> Id {
        assert!(num_components.len() == component_ids.len());
        let out_components = num_components.iter().fold(0, |acc, &x| acc + x);
        let base_ty = Type::Float(32);
        let ty = Type::Vector{ base: Box::new(base_ty.clone()), components: out_components };
        if args.iter().all(|arg| arg.is_constant()) && num_components.iter().all(|num| *num == 1) {
            // all args are scalar constants!
            let constant = module::Constant::Composite(ty, component_ids);
            self.ctxt.builder.define_constant(constant)
        } else {
            let scalar_ids = {
                num_components
                    .iter()
                    .zip(component_ids.iter())
                    .flat_map(|(num, id)| {
                        if *num > 1 {
                            let composite_ty = Type::Vector{ base: Box::new(base_ty.clone()), components: *num };
                            let composite_id = self.ctxt.builder.alloc_id();
                            self.block.emit_instruction(
                                OpLoad(
                                    self.ctxt.builder.define_type(&composite_ty),
                                    composite_id,
                                    *id,
                                    None,
                                )
                            );
                            (0..*num).map(|i| {
                                let scalar_id = self.ctxt.builder.alloc_id();
                                self.block.emit_instruction(
                                    OpCompositeExtract(
                                        self.ctxt.builder.define_type(&base_ty),
                                        scalar_id,
                                        composite_id,
                                        vec![LiteralInteger(i)],
                                    )
                                );
                                scalar_id
                            }).collect::<Vec<Id>>().into_iter()
                        } else {
                            vec![*id].into_iter()
                        }
                    }).collect::<Vec<Id>>()
            };

            let composite_id = self.ctxt.builder.alloc_id();
            self.block.emit_instruction(
                OpCompositeConstruct(self.ctxt.builder.define_type(&ty), composite_id, scalar_ids)
            );
            composite_id
        }
    }
}

fn extract_u32_from_operand(operand: &Operand) -> u32 {
        match *operand {
            Operand::Constant(ref c) => {
                match c.literal {
                    Literal::Value { value: Integral(ConstInt::U32(v)) } => v,
                    _ => bug!("Expected u32 constant `{:?}", operand)
                }
            }
            _ => bug!("Expected constant operand `{:?}`", operand)
        }
    }