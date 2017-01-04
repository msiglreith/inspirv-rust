
use rustc::mir;
use rustc::ty::Ty;
use rustc::ty::TypeFoldable;
use rustc::middle::const_val::ConstVal;

use rustc_const_math::ConstInt::*;
use rustc_const_math::ConstFloat::*;
use rustc_const_math::{ConstInt, ConstIsize, ConstUsize, ConstMathErr};

use {MirContext, BlockAndBuilder};
use context::CrateContext;
use lvalue::ValueRef;
use type_of;

use inspirv_builder::module::{self, ConstValue, ConstValueFloat};

/// A sized constant rvalue.
#[derive(Clone, Debug)]
pub struct Const<'tcx> {
    pub spv_val: ValueRef,
    pub ty: Ty<'tcx>
}

impl<'tcx> Const<'tcx> {
    pub fn new(spv_val: ValueRef, ty: Ty<'tcx>) -> Const<'tcx> {
        Const {
            spv_val: spv_val,
            ty: ty
        }
    }

    pub fn from_constval<'a>(ccx: &CrateContext<'a, 'tcx>,
                             cv: ConstVal,
                             ty: Ty<'tcx>)
                             -> Const<'tcx>
    {
        assert!(!ty.has_erasable_regions());

        let spv_ty = type_of::spv_type_of(ccx, ty).expect_no_ref();

        let const_val = match cv {
            ConstVal::Float(F32(v)) => module::Constant::Float(ConstValueFloat::F32(v)),
            ConstVal::Float(F64(v)) => module::Constant::Float(ConstValueFloat::F64(v)),
            ConstVal::Float(FInfer {..}) => bug!("MIR must not use `{:?}`", cv),

            ConstVal::Bool(v) => module::Constant::Scalar(ConstValue::Bool(v)),
            ConstVal::Integral(I8(v)) => bug!("Inspirv: `i8` is not supported for shaders `{:?}`", cv),
            ConstVal::Integral(I16(v)) => module::Constant::Scalar(ConstValue::I16(v)),
            ConstVal::Integral(I32(v)) => module::Constant::Scalar(ConstValue::I32(v)),
            ConstVal::Integral(I64(v)) => module::Constant::Scalar(ConstValue::I64(v)),
            ConstVal::Integral(Isize(v)) => {
                let i = v.as_i64(ccx.tcx().sess.target.int_type);
                module::Constant::Scalar(ConstValue::I64(i))
            },
            ConstVal::Integral(U8(v)) => bug!("Inspirv: `u8` is not supported for shaders `{:?}`", cv),
            ConstVal::Integral(U16(v)) => module::Constant::Scalar(ConstValue::U16(v)),
            ConstVal::Integral(U32(v)) => module::Constant::Scalar(ConstValue::U32(v)),
            ConstVal::Integral(U64(v)) => module::Constant::Scalar(ConstValue::U64(v)),
            ConstVal::Integral(Usize(v)) => {
                let u = v.as_u64(ccx.tcx().sess.target.uint_type);
                module::Constant::Scalar(ConstValue::U64(u))
            },

            ConstVal::Char(c) => bug!("Inspirv: `char` is (currently) not supported for shaders `{:?}`", cv),

            ConstVal::Integral(Infer(_)) |
            ConstVal::Integral(InferSigned(_)) |
            ConstVal::Str(_) | ConstVal::ByteStr(_) => bug!("MIR must not use `{:?}`", cv), // TODO: recheck string support later

            ConstVal::Struct(_) | ConstVal::Tuple(_) |
            ConstVal::Array(..) | ConstVal::Repeat(..) |
            ConstVal::Function(_) => bug!("MIR must not use `{:?}` (which refers to a local ID)", cv),
            ConstVal::Dummy => bug!(),
        };

        let constant_id = ccx.spv().borrow_mut().define_constant(const_val);
        Const::new(
            ValueRef {
                spvid: constant_id,
                spvty: spv_ty,
            },
            ty,
        )
    }
}

impl<'bcx, 'tcx> MirContext<'bcx, 'tcx> {
    pub fn trans_constant(&mut self,
                          bcx: &BlockAndBuilder<'bcx, 'tcx>,
                          constant: &mir::Constant<'tcx>)
                          -> Const<'tcx>
    {
        println!("trans_constant({:?})", constant);

        let ty = bcx.monomorphize(&constant.ty);
        let result = match constant.literal.clone() {
            mir::Literal::Item { def_id, substs } => {
                unimplemented!()
            }

            mir::Literal::Promoted { index } => {
                unimplemented!()
            }

            mir::Literal::Value { value } => {
                Const::from_constval(bcx.ccx(), value, ty)
            }
        };


        println!("trans_constant({:?}) = {:?}", constant, result);
        result
    }
}