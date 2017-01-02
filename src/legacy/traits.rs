use rustc::ty::{self, TyCtxt};
use rustc::hir::def_id::DefId;

use std::rc::Rc;
use rustc::traits::{self, Reveal};
use rustc::ty::subst::{Substs};
use rustc::ty::fold::TypeFoldable;
use syntax::ast::{Name, DUMMY_NODE_ID};
use syntax::codemap::{DUMMY_SP};

// The following is 99% from Miri (terminator.rs), with error handling from rustc trans

/// Trait method, which has to be resolved to an impl method.
pub fn resolve_trait_method<'a, 'tcx>(
    tcx: &TyCtxt<'a, 'tcx, 'tcx>,
    def_id: DefId,
    substs: &'tcx Substs<'tcx>
) -> (DefId, &'tcx Substs<'tcx>) {
    let trait_ref = ty::TraitRef::new(def_id, substs);
    let trait_id = trait_ref.def_id;
    let trait_ref = ty::Binder(trait_ref);
    match fulfill_obligation(tcx, trait_ref) {
        traits::VtableImpl(vtable_impl) => {
            let impl_did = vtable_impl.impl_def_id;
            let mname = tcx.item_name(def_id);
            // Create a concatenated set of substitutions which includes those from the impl
            // and those from the method:
            let substs = substs.rebase_onto(*tcx, trait_id, vtable_impl.substs);
            let mth = get_impl_method(*tcx, impl_did, substs, mname);

            (mth.method.def_id, mth.substs)
        }

        traits::VtableClosure(vtable_closure) =>
            (vtable_closure.closure_def_id, vtable_closure.substs.substs),

        traits::VtableFnPointer(_fn_ty) => {
            let _trait_closure_kind = tcx.lang_items.fn_trait_kind(trait_id).unwrap();
            unimplemented!()
        }

        traits::VtableObject(ref _data) => {
            unimplemented!()
        }
        vtable => unreachable!("resolved vtable bad vtable {:?} in trans", vtable),
    }
}

fn fulfill_obligation<'a, 'tcx>(
    tcx: &TyCtxt<'a, 'tcx, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>
) -> traits::Vtable<'tcx, ()> {
    let trait_ref = tcx.erase_regions(&trait_ref);

    tcx.infer_ctxt(None, None, Reveal::All).enter(|infcx| {
        let mut selcx = traits::SelectionContext::new(&infcx);

        let obligation = traits::Obligation::new(
            traits::ObligationCause::misc(DUMMY_SP, DUMMY_NODE_ID),
            trait_ref.to_poly_trait_predicate(),
        );

        let selection = match selcx.select(&obligation) {
            Ok(Some(selection)) => selection,
            Ok(None) => {
                // Ambiguity can happen when monomorphizing during trans
                // expands to some humongo type that never occurred
                // statically -- this humongo type can then overflow,
                // leading to an ambiguous result. So report this as an
                // overflow bug, since I believe this is the only case
                // where ambiguity can result.
                debug!("Encountered ambiguity selecting `{:?}` during trans, \
                        presuming due to overflow",
                       trait_ref);
                // NOTE: in trans, this is a tcx.sess.span_fatal(&self.span,...) error rather than a panic
                panic!("reached the recursion limit during monomorphization \
                        (selection ambiguity)");
            }
            Err(e) => {
                panic!("Encountered error `{:?}` selecting `{:?}` during trans",
                          e, trait_ref)
            }
        };

        // Currently, we use a fulfillment context to completely resolve
        // all nested obligations. This is because they can inform the
        // inference of the impl's type parameters.
        let mut fulfill_cx = traits::FulfillmentContext::new();
        let vtable = selection.map(|predicate| {
            fulfill_cx.register_predicate_obligation(&infcx, predicate);
        });
        infcx.drain_fulfillment_cx_or_panic(DUMMY_SP, &mut fulfill_cx, &vtable)
    })
}

#[derive(Debug)]
struct ImplMethod<'tcx> {
    method: ty::AssociatedItem,
    substs: &'tcx Substs<'tcx>,
    is_provided: bool,
}

/// Locates the applicable definition of a method, given its name.
fn get_impl_method<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    impl_def_id: DefId,
    substs: &'tcx Substs<'tcx>,
    name: Name,
) -> ImplMethod<'tcx> {
    assert!(!substs.needs_infer());

    let trait_def_id = tcx.trait_id_of_impl(impl_def_id).unwrap();
    let trait_def = tcx.lookup_trait_def(trait_def_id);

    match trait_def.ancestors(impl_def_id).defs(tcx, name, ty::AssociatedKind::Method).next() {
        Some(node_item) => {
            let substs = tcx.infer_ctxt(None, None, Reveal::All).enter(|infcx| {
                let substs = traits::translate_substs(&infcx, impl_def_id,
                                                      substs, node_item.node);
                tcx.lift(&substs).unwrap_or_else(|| {
                    bug!("trans::meth::get_impl_method: translate_substs \
                          returned {:?} which contains inference types/regions",
                         substs);
                })
            });
            ImplMethod {
                method: node_item.item,
                substs: substs,
                is_provided: node_item.node.is_from_trait(),
            }
        }
        None => {
            bug!("method {:?} not found in {:?}", name, impl_def_id)
        }
    }
}
