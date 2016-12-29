
use rustc::hir;
use rustc::ty::{self, Ty, TypeFoldable};

use syntax::ast::{IntTy, UintTy, FloatTy};

use inspirv::types::*;
use inspirv_builder::Type;

use super::context::CrateContext;
use super::attributes::{self, Attribute};

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

    pub fn ty(&self) -> &Type {
        match *self {
            SpvType::NoRef(ref ty) |
            SpvType::Ref { ref ty, .. } => ty,
        }
    }
}

pub fn spv_type_of<'a, 'tcx>(cx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>) -> SpvType {
    use self::SpvType::*;
    let tcx = cx.tcx();
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

        ty::TyRef(_, ty_mut) => {
            Ref {
                ty: spv_type_of(cx, ty_mut.ty).no_ref().unwrap(),
                mutable: ty_mut.mutbl == hir::Mutability::MutMutable,
                referent: None,
            }
        }

        ty::TyAdt(adt, subs) if adt.is_struct() => {
            let attrs = attributes::attributes(cx, adt.did);
            let internal_type = attrs.iter().find(|attr| match **attr {
                Attribute::Vector { .. } |
                Attribute::Matrix { .. } => true,
                _ => false,
            });
            let wrapper_type = attrs.iter().any(|attr| match *attr {
                Attribute::ConstBuffer |
                Attribute::Interface => true,
                _ => false,
            });
            if let Some(internal_type) = internal_type {
                match *internal_type {
                    Attribute::Vector { components } => {
                        let base = spv_type_of(cx, adt.struct_variant().fields[0].ty(tcx, subs)).no_ref().unwrap();
                        NoRef(Type::Vector {
                            base: Box::new(base),
                            components: components as u32,
                        })
                    }
                    Attribute::Matrix { rows, cols } => {
                        let base = spv_type_of(cx, adt.struct_variant().fields[0].ty(tcx, subs)).no_ref().unwrap();
                        if let Type::Vector { base, .. } = base {
                            NoRef(Type::Matrix {
                                base: base,
                                rows: rows as u32,
                                cols: cols as u32,
                            })
                        } else {
                            bug!("Unexpected matrix base type ({:?})", base)
                        }                            
                    }
                    _ => bug!("Unhandled internal type ({:?})", *internal_type),
                }
            } else if wrapper_type {
                spv_type_of(cx, adt.struct_variant().fields[0].ty(tcx, subs))
            } else {
                // an actual struct!
                // TODO: handle names
                NoRef(Type::Struct(
                    adt.struct_variant()
                       .fields
                       .iter()
                       .map(|field|
                            spv_type_of(cx,
                                field.ty(tcx, subs))
                            .no_ref().unwrap())
                       .collect::<Vec<_>>()))
            }    
        }

        _ => { println!("{:?}", t.sty); unimplemented!() },
    }
}
