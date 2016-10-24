
use rustc::mir::repr::*;
use rustc::middle::const_val::ConstVal::*;
use rustc_const_math::ConstInt;
use rustc::ty::{self, TyCtxt, Ty};
use syntax::parse::PResult;
use trans::{InspirvBlock, SpirvOperand, SpirvLvalue, SpirvType};
use inspirv::types::*;
use inspirv::core::instruction::*;
use inspirv_builder::module::{self, Type};
use inspirv::glsl::instruction as glsl;

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
    Add,
    Sub,
    Mul,
    Transpose,
    Inverse,
    OuterProduct,
    Normalize,
    Cross,
    Deref,
}

impl<'a: 'b, 'b: 'e, 'v: 'a, 'tcx: 'v ,'e> InspirvBlock<'a, 'b, 'v, 'tcx> {
    pub fn emit_intrinsic(&mut self, intrinsic: &Intrinsic, args: &[Operand<'tcx>], ret_ty: Ty<'tcx>) -> PResult<'e, Id> {
        use self::Intrinsic::*;
        let args_ops = args.iter().map(|arg| self.trans_operand(arg)).collect::<PResult<Vec<_>>>()?;
        let component_ids = args_ops.iter().filter_map(
                                |arg| match *arg {
                                    SpirvOperand::Constant(c, _) => Some(c),
                                    SpirvOperand::Consume(SpirvLvalue::Variable(_, SpirvType::Ref { referent, .. } , _)) => referent,
                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, ref op_ty, _)) => {
                                        let op_id = self.ctxt.builder.alloc_id();
                                        let op_load = OpLoad(self.ctxt.builder.define_type(op_ty), op_id, op_ptr_id, None);
                                        self.block.emit_instruction(op_load);
                                        Some(op_id)
                                    }
                                    _ => None
                                }).collect::<Vec<_>>();

        match *intrinsic {
            VectorNew(ref components) => {
                let ret_ty = self.ctxt.rust_ty_to_spirv_ref(ret_ty)?;
                self.emit_vector_new(components, args_ops, component_ids, &ret_ty)
            }
            Swizzle { components_out, components_in } => self.emit_swizzle(
                                                                    components_in,
                                                                    components_out,
                                                                    args,
                                                                    args_ops,
                                                                    component_ids),
            Shuffle { components_out, components_in0, components_in1 } => self.emit_shuffle(
                                                                            components_out,
                                                                            components_in0,
                                                                            components_in1,
                                                                            args,
                                                                            args_ops,
                                                                            component_ids),
            Add => self.emit_add(args_ops, component_ids),
            Sub => self.emit_sub(args_ops, component_ids),
            Mul => self.emit_mul(args_ops, component_ids),
            Transpose => self.emit_transpose(args_ops, component_ids),
            Inverse => self.emit_inverse(args_ops, component_ids),
            Normalize => self.emit_normalize(args_ops, component_ids),
            Cross => self.emit_cross(args_ops, component_ids),
            OuterProduct => self.emit_outer_product(args_ops, component_ids),
            Deref => Ok(component_ids[0]),
        }
    }

    fn emit_shuffle(&mut self,
        num_output_components: u32,
        num_input0_components: u32,
        num_input1_components: u32,
        args: &[Operand<'tcx>],
        args_ops: Vec<SpirvOperand>,
        component_ids: Vec<Id>
    ) -> PResult<'e, Id> {
        let ty = args_ops[0].get_ty().unwrap();
        if args_ops[2..].iter().all(|arg| arg.is_constant()) {
            // all args are constants!
            let result_id = self.ctxt.builder.alloc_id();
            // components
            let max_index = num_input0_components + num_input1_components - 1;
            let shuffle_components = args[2..].iter().map(|arg| {
                let index = extract_u32_from_operand(arg);
                if index > max_index { bug!{"inspirv: shuffle component {:?} out of range {:?}", arg, index} }
                LiteralInteger(index)
            }).collect::<Vec<_>>();            
            
            self.block.emit_instruction(
                OpVectorShuffle(
                    self.ctxt.builder.define_type(ty),
                    result_id,
                    component_ids[0],
                    component_ids[1],
                    shuffle_components,
                )
            );
            Ok(result_id)
        } else {
            panic!("Unhandled dynamic `shuffle4`")
        }
    }

    fn emit_swizzle(&mut self, num_input_components: u32, num_output_components: u32, args: &[Operand<'tcx>], args_ops: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        assert!(num_output_components as usize + 1 == component_ids.len());
        let ty = args_ops[0].get_ty().unwrap();
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
                    self.ctxt.builder.define_type(ty),
                    result_id,
                    component_ids[0],
                    component_ids[0],
                    components
                )
            );
            Ok(result_id)
        } else {
            panic!("Unhandled dynamic swizzle!")
        }
    }

    fn emit_vector_new(&mut self, num_components: &[u32], args: Vec<SpirvOperand>, component_ids: Vec<Id>, ret_ty: &SpirvType) -> PResult<'e, Id> {
        assert!(num_components.len() == component_ids.len());
        let out_components = num_components.iter().fold(0, |acc, &x| acc + x);
        let base_ty = if let Type::Vector { ref base, .. } = *ret_ty.ty() { base } else { return Err(self.ctxt.tcx.sess.struct_err("inspirv: expected vector type")); };
        let ty = Type::Vector{ base: base_ty.clone(), components: out_components };
        if args.iter().all(|arg| arg.is_constant()) && num_components.iter().all(|num| *num == 1) {
            // all args are scalar constants!
            let constant = module::Constant::Composite(ty, component_ids);
            Ok(self.ctxt.builder.define_constant(constant))
        } else {
            let scalar_ids = {
                num_components
                    .iter()
                    .zip(component_ids.iter())
                    .flat_map(|(num, id)| {
                        if *num > 1 {
                            (0..*num).map(|i| {
                                let scalar_id = self.ctxt.builder.alloc_id();
                                self.block.emit_instruction(
                                    OpCompositeExtract(
                                        self.ctxt.builder.define_type(&base_ty),
                                        scalar_id,
                                        *id,
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
            Ok(composite_id)
        }
    }

    // Addition for non-standard types (vector)
    fn emit_add(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        use trans::SpirvOperand::*;
        use trans::SpirvLvalue::*;
        use trans::SpirvType::*;

        let left_ty = {
            match args[0] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected add argument {:?}", args[0]),
            }
        };

        let right_ty = {
            match args[1] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected add argument {:?}", args[1]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();

        match (left_ty, right_ty) {
            (&Type::Vector { base: ref lbase, components: lcomponents },
             &Type::Vector { base: ref rbase, components: rcomponents }) if lbase == rbase && lcomponents == rcomponents => {
                match **lbase {
                    Type::Int(..) => {
                        self.block.emit_instruction(
                            OpIAdd(self.ctxt.builder.define_type(left_ty), result_id, component_ids[0], component_ids[1])
                        );
                    }

                    Type::Float(..) => {
                        self.block.emit_instruction(
                            OpFAdd(self.ctxt.builder.define_type(left_ty), result_id, component_ids[0], component_ids[1])
                        );
                    }

                    _ => { bug!("{:?}", (left_ty, right_ty)); }
                }
            }

            _ => { bug!("{:?}", (left_ty, right_ty)); }
        }
        
        Ok(result_id)
    }

    // Substraction for non-standard types (vector)
    fn emit_sub(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        use trans::SpirvOperand::*;
        use trans::SpirvLvalue::*;
        use trans::SpirvType::*;

        let left_ty = {
            match args[0] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected add argument {:?}", args[0]),
            }
        };

        let right_ty = {
            match args[1] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected add argument {:?}", args[1]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();

        match (left_ty, right_ty) {
            (&Type::Vector { base: ref lbase, components: lcomponents },
             &Type::Vector { base: ref rbase, components: rcomponents }) if lbase == rbase && lcomponents == rcomponents => {
                // TODO
             }

            _ => { bug!("{:?}", (left_ty, right_ty)); }
        }
        
        Ok(result_id)
    }

    // Multiplication for non-standard types (matrix and vector)
    fn emit_mul(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        use trans::SpirvOperand::*;
        use trans::SpirvLvalue::*;
        use trans::SpirvType::*;

        let left_ty = {
            match args[0] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected mul argument {:?}", args[0]),
            }
        };

        let right_ty = {
            match args[1] {
                Consume(Variable(_, NoRef(ref ty), _)) |
                Constant(_, NoRef(ref ty)) => ty,
                _ => bug!("Unexpected mul argument {:?}", args[1]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();

        match (left_ty, right_ty) {
            (&Type::Matrix { base: ref lbase, rows: lrows, cols: lcols },
             &Type::Matrix { base: ref rbase, rows: rrows, cols: rcols }) if lbase == rbase && lcols == rrows => {
                let result_ty = Type::Matrix { base: lbase.clone(), rows: lrows, cols: rcols };
                self.block.emit_instruction(
                    OpMatrixTimesMatrix(self.ctxt.builder.define_type(&result_ty), result_id, component_ids[0], component_ids[1])
                );
            }

            (&Type::Matrix { base: ref lbase, rows, cols },
             &Type::Vector { base: ref rbase, components }) if lbase == rbase && cols == components => {
                let result_ty = Type::Vector { base: rbase.clone(), components: rows };
                self.block.emit_instruction(
                    OpMatrixTimesVector(self.ctxt.builder.define_type(&result_ty), result_id, component_ids[0], component_ids[1])
                );
            }

            (&Type::Vector { base: ref lbase, components },
             &Type::Matrix { base: ref rbase, rows, cols }) if lbase == rbase && rows == components => {
                let result_ty = Type::Vector { base: lbase.clone(), components: cols };
                self.block.emit_instruction(
                    OpVectorTimesMatrix(self.ctxt.builder.define_type(&result_ty), result_id, component_ids[0], component_ids[1])
                );
            }

            (&Type::Matrix { ref base, .. }, ty) if *ty == **base => {
               self.block.emit_instruction(
                    OpMatrixTimesScalar(self.ctxt.builder.define_type(ty), result_id, component_ids[0], component_ids[1])
                ); 
            }

            (ty, &Type::Matrix { ref base, .. }) if *ty == **base => {
                self.block.emit_instruction(
                    OpMatrixTimesScalar(self.ctxt.builder.define_type(ty), result_id, component_ids[1], component_ids[0])
                );
            }

            (&Type::Vector { base: ref lbase, components: lcomponents },
             &Type::Vector { base: ref rbase, components: rcomponents }) if lbase == rbase && lcomponents == rcomponents => {
                self.block.emit_instruction(
                    OpDot(self.ctxt.builder.define_type(lbase), result_id, component_ids[0], component_ids[1])
                );
             }

            _ => { bug!("{:?}", (left_ty, right_ty)); }
        }
        
        Ok(result_id)
    }

    fn emit_transpose(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        // expect a matrix type
        let result_ty = {
            use trans::SpirvOperand::*;
            use trans::SpirvLvalue::*;
            use trans::SpirvType::*;
            match args[0] {
                Consume(Variable(_, NoRef(Type::Matrix { ref base, rows, cols }), _)) |
                Constant(_, NoRef(Type::Matrix { ref base, rows, cols })) => Type::Matrix { base: base.clone(), rows: cols, cols: rows },
                _ => bug!("Unexpected transpose argument {:?}", args[0]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();
        self.block.emit_instruction(
            OpTranspose(self.ctxt.builder.define_type(&result_ty), result_id, component_ids[0])
        );
        Ok(result_id)
    }

    fn emit_inverse(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        // expect a matrix type
        let result_ty = {
            use trans::SpirvOperand::*;
            use trans::SpirvLvalue::*;
            use trans::SpirvType::*;
            match args[0] {
                Consume(Variable(_, NoRef(Type::Matrix { ref base, rows, cols }), _)) |
                Constant(_, NoRef(Type::Matrix { ref base, rows, cols })) if rows == cols => Type::Matrix { base: base.clone(), rows: rows, cols: cols },
                _ => bug!("Unexpected inverse argument {:?}", args[0]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();
        let ext_glsl = self.ctxt.builder.import_extension("GLSL.std.450");
        self.block.emit_glsl_instruction(ext_glsl, glsl::OpCode::MatrixInverse, result_id, self.ctxt.builder.define_type(&result_ty), vec![component_ids[0]]);
        Ok(result_id)
    }

    fn emit_normalize(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        // expect a vector type
        let result_ty = {
            use trans::SpirvOperand::*;
            use trans::SpirvLvalue::*;
            use trans::SpirvType::*;
            match args[0] {
                Consume(Variable(_, NoRef(Type::Vector { ref base, components }), _)) |
                Constant(_, NoRef(Type::Vector { ref base, components })) => Type::Vector { base: base.clone(), components: components },
                _ => bug!("Unexpected normalize argument {:?}", args[0]),
            }
        };

        let result_id = self.ctxt.builder.alloc_id();
        let ext_glsl = self.ctxt.builder.import_extension("GLSL.std.450");
        self.block.emit_glsl_instruction(ext_glsl, glsl::OpCode::Normalize, result_id, self.ctxt.builder.define_type(&result_ty), vec![component_ids[0]]);
        Ok(result_id)
    }

    fn emit_cross(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        // expect a vec3 type
        use trans::SpirvOperand::*;
        use trans::SpirvLvalue::*;
        use trans::SpirvType::*;

        let left_ty = {
            match args[0] {
                Consume(Variable(_, NoRef(Type::Vector { ref base, components: 3 }), _)) |
                Constant(_, NoRef(Type::Vector { ref base, components: 3 })) => Type::Vector { base: base.clone(), components: 3 },
                _ => bug!("Unexpected cross argument {:?}", args[0]),
            }
        };

        let right_ty = {
            match args[1] {
                Consume(Variable(_, NoRef(Type::Vector { ref base, components: 3 }), _)) |
                Constant(_, NoRef(Type::Vector { ref base, components: 3 })) => Type::Vector { base: base.clone(), components: 3 },
                _ => bug!("Unexpected cross argument {:?}", args[1]),
            }
        };

        // TODO: check same base types

        let result_id = self.ctxt.builder.alloc_id();
        let ext_glsl = self.ctxt.builder.import_extension("GLSL.std.450");
        self.block.emit_glsl_instruction(ext_glsl, glsl::OpCode::Cross, result_id, self.ctxt.builder.define_type(&left_ty), vec![component_ids[0], component_ids[1]]);
        Ok(result_id)
    }

    fn emit_outer_product(&mut self, args: Vec<SpirvOperand>, component_ids: Vec<Id>) -> PResult<'e, Id> {
        // expect a vector type
        use trans::SpirvOperand::*;
        use trans::SpirvLvalue::*;
        use trans::SpirvType::*;

        let left_ty = {
            match args[0] {
                Consume(Variable(_, NoRef(Type::Vector { ref base, components }), _)) |
                Constant(_, NoRef(Type::Vector { ref base, components })) => Type::Vector { base: base.clone(), components: components },
                _ => bug!("Unexpected cross argument {:?}", args[0]),
            }
        };

        let right_ty = {
            match args[1] {
                Consume(Variable(_, NoRef(Type::Vector { ref base, components }), _)) |
                Constant(_, NoRef(Type::Vector { ref base, components })) => Type::Vector { base: base.clone(), components: components },
                _ => bug!("Unexpected cross argument {:?}", args[1]),
            }
        };

        // TODO: check same types

        let result_id = self.ctxt.builder.alloc_id();
        self.block.emit_instruction(
            OpOuterProduct(self.ctxt.builder.define_type(&left_ty), result_id, component_ids[0], component_ids[1])
        );
        Ok(result_id)
    }
}

fn extract_u32_from_operand(operand: &Operand) -> u32 {
        match *operand {
            Operand::Constant(ref c) => {
                match c.literal {
                    Literal::Value { value: Integral(ConstInt::U32(v)) } => v,
                    _ => bug!("Expected u32 constant {:?}", operand)
                }
            }
            _ => bug!("Expected constant operand `{:?}`", operand)
        }
    }