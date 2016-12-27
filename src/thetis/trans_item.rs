
use arena::TypedArena;
use rustc::dep_graph::DepNode;
use rustc_const_eval::fatal_const_eval_err;
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::hir::map::DefPathData;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::ty::subst::Substs;
use syntax::ast::{self, NodeId};
use super::monomorphize::{self, Instance};
use super::context::{CrateContext, SharedCrateContext};
use super::{FunctionContext};
use super::{trans_function, trans_static};

use std::fmt::Write;
use std::iter;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum TransItem<'tcx> {
    Fn(Instance<'tcx>),
    Static(NodeId)
}

impl<'a, 'tcx> TransItem<'tcx> {
    pub fn predefine(&self, ccx: &CrateContext<'a, 'tcx>) {
        // TODO:
    }

    pub fn define(&self, ccx: &CrateContext<'a, 'tcx>) {
        match *self {
            TransItem::Static(node_id) => {
                let def_id = ccx.tcx().map.local_def_id(node_id);
                let _task = ccx.tcx().dep_graph.in_task(DepNode::TransCrateItem(def_id));
                let item = ccx.tcx().map.expect_item(node_id);
                if let hir::ItemStatic(_, m, _) = item.node {
                    match trans_static(&ccx, m, item.id, &item.attrs) {
                        Ok(_) => { /* Cool, everything's alright. */ },
                        Err(err) => {
                            // FIXME: shouldn't this be a `span_err`?
                            fatal_const_eval_err(
                                ccx.tcx(), &err, item.span, "static");
                        }
                    };
                } else {
                    span_bug!(item.span, "Mismatch between hir::Item type and TransItem type")
                }
            }
            TransItem::Fn(instance) => {
                let _task = ccx.tcx().dep_graph.in_task(
                    DepNode::TransCrateItem(instance.def));

                trans_instance(&ccx, instance);
            }
        }
    }

    /// Returns true if there has to be a local copy of this TransItem in every
    /// codegen unit that references it (as with inlined functions, for example)
    pub fn needs_local_copy(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> bool {
        // Currently everything that is instantiated only on demand is done so
        // with "internal" linkage, so we need a copy to be present in every
        // codegen unit.
        // This is coincidental: We could also instantiate something only if it
        // is referenced (e.g. a regular, private function) but place it in its
        // own codegen unit with "external" linkage.
        self.is_instantiated_only_on_demand(tcx)
    }

    pub fn is_instantiated_only_on_demand(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> bool {
        match *self {
            TransItem::Fn(ref instance) => {
                !instance.def.is_local() ||
                instance.substs.types().next().is_some() ||
                is_closure(tcx, instance.def)
            }
            TransItem::Static(..)   => false,
        }
    }

    pub fn to_string(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> String {
        let hir_map = &tcx.map;

        return match *self {
            TransItem::Fn(instance) => {
                to_string_internal(tcx, "fn ", instance)
            },
            TransItem::Static(node_id) => {
                let def_id = hir_map.local_def_id(node_id);
                let instance = Instance::new(def_id, tcx.intern_substs(&[]));
                to_string_internal(tcx, "static ", instance)
            },
        };

        fn to_string_internal<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                        prefix: &str,
                                        instance: Instance<'tcx>)
                                        -> String {
            let mut result = String::with_capacity(32);
            result.push_str(prefix);
            let printer = DefPathBasedNames::new(tcx, false, false);
            printer.push_instance_as_string(instance, &mut result);
            result
        }
    }

    pub fn is_generic_fn(&self) -> bool {
        match *self {
            TransItem::Fn(ref instance) => {
                instance.substs.types().next().is_some()
            }
            TransItem::Static(..)   => false,
        }
    }
}

//=-----------------------------------------------------------------------------
// TransItem String Keys
//=-----------------------------------------------------------------------------

// The code below allows for producing a unique string key for a trans item.
// These keys are used by the handwritten auto-tests, so they need to be
// predictable and human-readable.
//
// Note: A lot of this could looks very similar to what's already in the
//       ppaux module. It would be good to refactor things so we only have one
//       parameterizable implementation for printing types.

/// Same as `unique_type_name()` but with the result pushed onto the given
/// `output` parameter.
pub struct DefPathBasedNames<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    omit_disambiguators: bool,
    omit_local_crate_name: bool,
}

impl<'a, 'tcx> DefPathBasedNames<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>,
               omit_disambiguators: bool,
               omit_local_crate_name: bool)
               -> Self {
        DefPathBasedNames {
            tcx: tcx,
            omit_disambiguators: omit_disambiguators,
            omit_local_crate_name: omit_local_crate_name,
        }
    }

    pub fn push_type_name(&self, t: Ty<'tcx>, output: &mut String) {
        match t.sty {
            ty::TyBool              => output.push_str("bool"),
            ty::TyChar              => output.push_str("char"),
            ty::TyStr               => output.push_str("str"),
            ty::TyNever             => output.push_str("!"),
            ty::TyInt(ast::IntTy::Is)    => output.push_str("isize"),
            ty::TyInt(ast::IntTy::I8)    => output.push_str("i8"),
            ty::TyInt(ast::IntTy::I16)   => output.push_str("i16"),
            ty::TyInt(ast::IntTy::I32)   => output.push_str("i32"),
            ty::TyInt(ast::IntTy::I64)   => output.push_str("i64"),
            ty::TyUint(ast::UintTy::Us)   => output.push_str("usize"),
            ty::TyUint(ast::UintTy::U8)   => output.push_str("u8"),
            ty::TyUint(ast::UintTy::U16)  => output.push_str("u16"),
            ty::TyUint(ast::UintTy::U32)  => output.push_str("u32"),
            ty::TyUint(ast::UintTy::U64)  => output.push_str("u64"),
            ty::TyFloat(ast::FloatTy::F32) => output.push_str("f32"),
            ty::TyFloat(ast::FloatTy::F64) => output.push_str("f64"),
            ty::TyAdt(adt_def, substs) => {
                self.push_def_path(adt_def.did, output);
                self.push_type_params(substs, iter::empty(), output);
            },
            ty::TyTuple(component_types) => {
                output.push('(');
                for &component_type in component_types {
                    self.push_type_name(component_type, output);
                    output.push_str(", ");
                }
                if !component_types.is_empty() {
                    output.pop();
                    output.pop();
                }
                output.push(')');
            },
            ty::TyBox(inner_type) => {
                output.push_str("Box<");
                self.push_type_name(inner_type, output);
                output.push('>');
            },
            ty::TyRawPtr(ty::TypeAndMut { ty: inner_type, mutbl } ) => {
                output.push('*');
                match mutbl {
                    hir::MutImmutable => output.push_str("const "),
                    hir::MutMutable => output.push_str("mut "),
                }

                self.push_type_name(inner_type, output);
            },
            ty::TyRef(_, ty::TypeAndMut { ty: inner_type, mutbl }) => {
                output.push('&');
                if mutbl == hir::MutMutable {
                    output.push_str("mut ");
                }

                self.push_type_name(inner_type, output);
            },
            ty::TyArray(inner_type, len) => {
                output.push('[');
                self.push_type_name(inner_type, output);
                write!(output, "; {}", len).unwrap();
                output.push(']');
            },
            ty::TySlice(inner_type) => {
                output.push('[');
                self.push_type_name(inner_type, output);
                output.push(']');
            },
            ty::TyDynamic(ref trait_data, ..) => {
                if let Some(principal) = trait_data.principal() {
                    self.push_def_path(principal.def_id(), output);
                    self.push_type_params(principal.skip_binder().substs,
                        trait_data.projection_bounds(),
                        output);
                }
            },
            ty::TyFnDef(.., &ty::BareFnTy{ unsafety, abi, ref sig } ) |
            ty::TyFnPtr(&ty::BareFnTy{ unsafety, abi, ref sig } ) => {
                if unsafety == hir::Unsafety::Unsafe {
                    output.push_str("unsafe ");
                }

                output.push_str("fn(");

                let sig = self.tcx.erase_late_bound_regions_and_normalize(sig);

                if !sig.inputs().is_empty() {
                    for &parameter_type in sig.inputs() {
                        self.push_type_name(parameter_type, output);
                        output.push_str(", ");
                    }
                    output.pop();
                    output.pop();
                }

                if sig.variadic {
                    if !sig.inputs().is_empty() {
                        output.push_str(", ...");
                    } else {
                        output.push_str("...");
                    }
                }

                output.push(')');

                if !sig.output().is_nil() {
                    output.push_str(" -> ");
                    self.push_type_name(sig.output(), output);
                }
            },
            ty::TyClosure(def_id, ref closure_substs) => {
                self.push_def_path(def_id, output);
                let generics = self.tcx.item_generics(self.tcx.closure_base_def_id(def_id));
                let substs = closure_substs.substs.truncate_to(self.tcx, generics);
                self.push_type_params(substs, iter::empty(), output);
            }
            ty::TyError |
            ty::TyInfer(_) |
            ty::TyProjection(..) |
            ty::TyParam(_) |
            ty::TyAnon(..) => {
                bug!("DefPathBasedNames: Trying to create type name for \
                                         unexpected type: {:?}", t);
            }
        }
    }

    pub fn push_def_path(&self,
                         def_id: DefId,
                         output: &mut String) {
        let def_path = self.tcx.def_path(def_id);

        // some_crate::
        if !(self.omit_local_crate_name && def_id.is_local()) {
            output.push_str(&self.tcx.crate_name(def_path.krate).as_str());
            output.push_str("::");
        }

        // foo::bar::ItemName::
        for part in self.tcx.def_path(def_id).data {
            if self.omit_disambiguators {
                write!(output, "{}::", part.data.as_interned_str()).unwrap();
            } else {
                write!(output, "{}[{}]::",
                       part.data.as_interned_str(),
                       part.disambiguator).unwrap();
            }
        }

        // remove final "::"
        output.pop();
        output.pop();
    }

    fn push_type_params<I>(&self,
                            substs: &Substs<'tcx>,
                            projections: I,
                            output: &mut String)
        where I: Iterator<Item=ty::PolyExistentialProjection<'tcx>>
    {
        let mut projections = projections.peekable();
        if substs.types().next().is_none() && projections.peek().is_none() {
            return;
        }

        output.push('<');

        for type_parameter in substs.types() {
            self.push_type_name(type_parameter, output);
            output.push_str(", ");
        }

        for projection in projections {
            let projection = projection.skip_binder();
            let name = &projection.item_name.as_str();
            output.push_str(name);
            output.push_str("=");
            self.push_type_name(projection.ty, output);
            output.push_str(", ");
        }

        output.pop();
        output.pop();

        output.push('>');
    }

    pub fn push_instance_as_string(&self,
                                   instance: Instance<'tcx>,
                                   output: &mut String) {
        self.push_def_path(instance.def, output);
        self.push_type_params(instance.substs, iter::empty(), output);
    }
}

pub fn is_closure(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.def_key(def_id).disambiguated_data.data == DefPathData::ClosureExpr
}

pub fn trans_instance<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, instance: Instance<'tcx>) {
    // this is an info! to allow collecting monomorphization statistics
    info!("trans_instance({})", instance);

    // let _icx = push_ctxt("trans_instance");

    let fn_ty = ccx.tcx().item_type(instance.def);
    let fn_ty = ccx.tcx().erase_regions(&fn_ty);
    let fn_ty = monomorphize::apply_param_substs(ccx.shared(), instance.substs, &fn_ty);

    // ccx.stats().n_closures.set(ccx.stats().n_closures.get() + 1);

    let (arena, fcx): (TypedArena<_>, FunctionContext);
    arena = TypedArena::new();
    fcx = FunctionContext::new(ccx,
                               Some(instance),
                               &arena);

    if fcx.mir.is_none() {
        bug!("attempted translation of `{}` w/o MIR", instance);
    }

    trans_function(&fcx);
}
