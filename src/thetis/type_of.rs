
use rustc::ty::{self, Ty, TypeFoldable};

use syntax::ast::{IntTy, UintTy, FloatTy};

use inspirv::types::*;
use inspirv_builder::Type;

use super::context::CrateContext;

pub enum SpvType {
    NoRef(Type),
    Ref {
        ty: Type,
        mutable: bool,
        referent: Option<Id>,
    }
}

impl SpvType {
    pub fn no_ref(self) -> Option<Type> {
        match self {
            SpvType::NoRef(t) => Some(t),
            _ => None,
        }
    }
}

pub fn spv_type_of<'a, 'tcx>(cx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>) -> SpvType {
    use self::SpvType::*;
    match t.sty {
        ty::TyBool => NoRef(Type::Bool),
        ty::TyInt(IntTy::I8)      => NoRef(Type::Int(8, true)),
        ty::TyInt(IntTy::I16)     => NoRef(Type::Int(16, true)),
        ty::TyInt(IntTy::Is) |
        ty::TyInt(IntTy::I32)     => NoRef(Type::Int(32, true)), // isize
        ty::TyInt(IntTy::I64)     => NoRef(Type::Int(64, true)),
        ty::TyChar |
        ty::TyUint(UintTy::U8)    => NoRef(Type::Int(8, false)),
        ty::TyUint(UintTy::U16)   => NoRef(Type::Int(16, false)),
        ty::TyUint(UintTy::Us) |
        ty::TyUint(UintTy::U32)   => NoRef(Type::Int(32, false)), // usize
        ty::TyUint(UintTy::U64)   => NoRef(Type::Int(64, false)),
        ty::TyFloat(FloatTy::F32) => NoRef(Type::Float(32)),
        ty::TyFloat(FloatTy::F64) => NoRef(Type::Float(64)),
        ty::TyArray(_ty, _len)    => unimplemented!(),

        // TyNever:
        //  Some weird case, appearing sometimes in the code for whatever reason
        //  Often as supposed temporary variables, which are never really used
        // TyTuple(&[]):
        //  Rust seems to emit () instead of void for function return types
        ty::TyNever => NoRef(Type::Void),
        ty::TyTuple(tys) if tys.is_empty() => NoRef(Type::Void),
        ty::TyTuple(tys) => NoRef(Type::Struct(
            tys.iter().map(|ty| spv_type_of(cx, ty).no_ref().unwrap()).collect::<Vec<_>>())),

        _ => { println!("{:?}", t.sty); unimplemented!() },
    }
}
