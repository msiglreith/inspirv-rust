
use super::*;
use rustc::ty::subst::Subst;
use rustc::ty::fold::{TypeFolder, TypeFoldable};
use rustc::util::ppaux;
use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instance<'tcx> {
    pub def: DefId,
    pub substs: &'tcx Substs<'tcx>,
}

impl<'tcx> fmt::Display for Instance<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ppaux::parameterized(f, &self.substs, self.def, &[])
    }
}

impl<'a, 'tcx> Instance<'tcx> {
    pub fn new(def_id: DefId, substs: &'tcx Substs<'tcx>)
               -> Instance<'tcx> {
        assert!(substs.regions().all(|&r| r == ty::ReErased));
        Instance { def: def_id, substs: substs }
    }
    pub fn mono(scx: &SharedCrateContext<'a, 'tcx>, def_id: DefId) -> Instance<'tcx> {
        Instance::new(def_id, scx.empty_substs_for_def_id(def_id))
    }

    pub fn symbol_name(self, scx: &SharedCrateContext<'a, 'tcx>) -> String {
        let Instance { def: def_id, substs } = self;

        debug!("symbol_name(def_id={:?}, substs={:?})",
               def_id, substs);

        let node_id = scx.tcx().hir.as_local_node_id(def_id);

        if let Some(id) = node_id {
            if scx.sess().plugin_registrar_fn.get() == Some(id) {
                let svh = &scx.link_meta().crate_hash;
                let idx = def_id.index;
                return scx.sess().generate_plugin_registrar_symbol(svh, idx);
            }
            if scx.sess().derive_registrar_fn.get() == Some(id) {
                let svh = &scx.link_meta().crate_hash;
                let idx = def_id.index;
                return scx.sess().generate_derive_registrar_symbol(svh, idx);
            }
        }

        return scx.tcx().item_name(def_id).as_str().to_string();
    }

    /// For associated constants from traits, return the impl definition.
    pub fn resolve_const(&self, scx: &SharedCrateContext<'a, 'tcx>) -> Self {
        if let Some(trait_id) = scx.tcx().trait_of_item(self.def) {
            let trait_ref = ty::TraitRef::new(trait_id, self.substs);
            let trait_ref = ty::Binder(trait_ref);
            let vtable = fulfill_obligation(scx, DUMMY_SP, trait_ref);
            if let traits::VtableImpl(vtable_impl) = vtable {
                let name = scx.tcx().item_name(self.def);
                let ac = scx.tcx().associated_items(vtable_impl.impl_def_id)
                    .find(|item| item.kind == ty::AssociatedKind::Const && item.name == name);
                if let Some(ac) = ac {
                    return Instance::new(ac.def_id, vtable_impl.substs);
                }
            }
        }

        *self
    }
}

/// Monomorphizes a type from the AST by first applying the in-scope
/// substitutions and then normalizing any associated types.
pub fn apply_param_substs<'a, 'tcx, T>(scx: &SharedCrateContext<'a, 'tcx>,
                                       param_substs: &Substs<'tcx>,
                                       value: &T)
                                       -> T
    where T: TransNormalize<'tcx>
{
    let tcx = scx.tcx();
    debug!("apply_param_substs(param_substs={:?}, value={:?})", param_substs, value);
    let substituted = value.subst(tcx, param_substs);
    let substituted = scx.tcx().erase_regions(&substituted);
    AssociatedTypeNormalizer::new(scx).fold(&substituted)
}

struct AssociatedTypeNormalizer<'a, 'b: 'a, 'gcx: 'b> {
    shared: &'a SharedCrateContext<'b, 'gcx>,
}

impl<'a, 'b, 'gcx> AssociatedTypeNormalizer<'a, 'b, 'gcx> {
    fn new(shared: &'a SharedCrateContext<'b, 'gcx>) -> Self {
        AssociatedTypeNormalizer {
            shared: shared,
        }
    }

    fn fold<T:TypeFoldable<'gcx>>(&mut self, value: &T) -> T {
        if !value.has_projection_types() {
            value.clone()
        } else {
            value.fold_with(self)
        }
    }
}

impl<'a, 'b, 'gcx> TypeFolder<'gcx, 'gcx> for AssociatedTypeNormalizer<'a, 'b, 'gcx> {
    fn tcx<'c>(&'c self) -> TyCtxt<'c, 'gcx, 'gcx> {
        self.shared.tcx()
    }

    fn fold_ty(&mut self, ty: Ty<'gcx>) -> Ty<'gcx> {
        if !ty.has_projection_types() {
            ty
        } else {
            self.shared.project_cache().memoize(ty, || {
                debug!("AssociatedTypeNormalizer: ty={:?}", ty);
                self.shared.tcx().normalize_associated_type(&ty)
            })
        }
    }
}