
use rustc::hir;
use rustc::hir::map as hir_map;
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::mir::{self, Location};
use rustc::mir::visit as mir_visit;
use rustc::mir::visit::Visitor as MirVisitor;
use rustc::traits;
use rustc::ty::subst::Substs;
use rustc::ty::{self, Ty, TypeFoldable, TyCtxt};
use rustc_trans::util::nodemap::{FxHashMap, FxHashSet, DefIdMap};
use rustc::ty::adjustment::CustomCoerceUnsized;
use rustc_const_eval as const_eval;
use thetis::{SharedCrateContext};
use thetis::monomorphize::{self, Instance};
use thetis::trans_item::{DefPathBasedNames, TransItem};
use syntax_pos::{DUMMY_SP};

use thetis::{custom_coerce_unsize_info, fulfill_obligation};

/// Maps every translation item to all translation items it references in its
/// body.
pub struct InliningMap<'tcx> {
    // Maps a source translation item to a range of target translation items
    // The two numbers in the tuple are the start (inclusive) and
    // end index (exclusive) within the `targets` vecs.
    index: FxHashMap<TransItem<'tcx>, (usize, usize)>,
    targets: Vec<TransItem<'tcx>>,
}

impl<'tcx> InliningMap<'tcx> {
    fn new() -> InliningMap<'tcx> {
        InliningMap {
            index: FxHashMap(),
            targets: Vec::new(),
        }
    }

    fn record_inlining_canditates<I>(&mut self,
                                     source: TransItem<'tcx>,
                                     targets: I)
        where I: Iterator<Item=TransItem<'tcx>>
    {
        assert!(!self.index.contains_key(&source));

        let start_index = self.targets.len();
        self.targets.extend(targets);
        let end_index = self.targets.len();
        self.index.insert(source, (start_index, end_index));
    }
}

pub fn collect_crate_translation_items<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>)
                                                 -> (FxHashSet<TransItem<'tcx>>,
                                                     InliningMap<'tcx>) {
    // We are not tracking dependencies of this pass as it has to be re-executed
    // every time no matter what.
    scx.tcx().dep_graph.with_ignore(|| {
        let roots = collect_roots(scx);

        debug!("Building translation item graph, beginning at roots");
        let mut visited = FxHashSet();
        let mut recursion_depths = DefIdMap();
        let mut inlining_map = InliningMap::new();

        for root in roots {
            collect_items_rec(scx,
                              root,
                              &mut visited,
                              &mut recursion_depths,
                              &mut inlining_map);
        }

        (visited, inlining_map)
    })
}

// Find all non-generic items by walking the HIR. These items serve as roots to
// start monomorphizing from.
fn collect_roots<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>) -> Vec<TransItem<'tcx>> {
    debug!("Collecting roots");
    let mut roots = Vec::new();

    {
        let mut visitor = RootCollector {
            scx: scx,
            output: &mut roots,
        };

        scx.tcx().map.krate().visit_all_item_likes(&mut visitor);
    }

    roots
}

// Collect all monomorphized translation items reachable from `starting_point`
fn collect_items_rec<'a, 'tcx: 'a>(scx: &SharedCrateContext<'a, 'tcx>,
                                   starting_point: TransItem<'tcx>,
                                   visited: &mut FxHashSet<TransItem<'tcx>>,
                                   recursion_depths: &mut DefIdMap<usize>,
                                   inlining_map: &mut InliningMap<'tcx>) {
    if !visited.insert(starting_point.clone()) {
        // We've been here already, no need to search again.
        return;
    }
    debug!("BEGIN collect_items_rec({})", starting_point.to_string(scx.tcx()));

    let mut neighbors = Vec::new();
    let recursion_depth_reset;

    match starting_point {
        TransItem::Static(node_id) => {
            let def_id = scx.tcx().map.local_def_id(node_id);
            recursion_depth_reset = None;

            // Scan the MIR in order to find function calls and closures
            let mir = scx.tcx().item_mir(def_id);

            let empty_substs = scx.empty_substs_for_def_id(def_id);
            let visitor = MirNeighborCollector {
                scx: scx,
                mir: &mir,
                output: &mut neighbors,
                param_substs: empty_substs
            };

            visit_mir_and_promoted(visitor, &mir);
        }
        TransItem::Fn(instance) => {
            // Keep track of the monomorphization recursion depth
            recursion_depth_reset = Some(check_recursion_limit(scx.tcx(),
                                                               instance,
                                                               recursion_depths));
            check_type_length_limit(scx.tcx(), instance);

            // Scan the MIR in order to find function calls, closures, and
            // drop-glue
            let mir = scx.tcx().item_mir(instance.def);

            let visitor = MirNeighborCollector {
                scx: scx,
                mir: &mir,
                output: &mut neighbors,
                param_substs: instance.substs
            };

            visit_mir_and_promoted(visitor, &mir);
        }
    }

    record_inlining_canditates(scx.tcx(), starting_point, &neighbors[..], inlining_map);

    for neighbour in neighbors {
        collect_items_rec(scx, neighbour, visited, recursion_depths, inlining_map);
    }

    if let Some((def_id, depth)) = recursion_depth_reset {
        recursion_depths.insert(def_id, depth);
    }

    debug!("END collect_items_rec({})", starting_point.to_string(scx.tcx()));
}

// There are no translation items for constants themselves but their
// initializers might still contain something that produces translation items,
// such as cast that introduce a new vtable.
fn collect_const_item_neighbours<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                           def_id: DefId,
                                           substs: &'tcx Substs<'tcx>,
                                           output: &mut Vec<TransItem<'tcx>>)
{
    // Scan the MIR in order to find function calls, closures, and
    // drop-glue
    let mir = scx.tcx().item_mir(def_id);

    let visitor = MirNeighborCollector {
        scx: scx,
        mir: &mir,
        output: output,
        param_substs: substs
    };

    visit_mir_and_promoted(visitor, &mir);
}

fn record_inlining_canditates<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                        caller: TransItem<'tcx>,
                                        callees: &[TransItem<'tcx>],
                                        inlining_map: &mut InliningMap<'tcx>) {
    let is_inlining_candidate = |trans_item: &TransItem<'tcx>| {
        trans_item.needs_local_copy(tcx)
    };

    let inlining_candidates = callees.into_iter()
                                     .map(|x| *x)
                                     .filter(is_inlining_candidate);

    inlining_map.record_inlining_canditates(caller, inlining_candidates);
}

/// For given pair of source and target type that occur in an unsizing coercion,
/// this function finds the pair of types that determines the vtable linking
/// them.
///
/// For example, the source type might be `&SomeStruct` and the target type\
/// might be `&SomeTrait` in a cast like:
///
/// let src: &SomeStruct = ...;
/// let target = src as &SomeTrait;
///
/// Then the output of this function would be (SomeStruct, SomeTrait) since for
/// constructing the `target` fat-pointer we need the vtable for that pair.
///
/// Things can get more complicated though because there's also the case where
/// the unsized type occurs as a field:
///
/// ```rust
/// struct ComplexStruct<T: ?Sized> {
///    a: u32,
///    b: f64,
///    c: T
/// }
/// ```
///
/// In this case, if `T` is sized, `&ComplexStruct<T>` is a thin pointer. If `T`
/// is unsized, `&SomeStruct` is a fat pointer, and the vtable it points to is
/// for the pair of `T` (which is a trait) and the concrete type that `T` was
/// originally coerced from:
///
/// let src: &ComplexStruct<SomeStruct> = ...;
/// let target = src as &ComplexStruct<SomeTrait>;
///
/// Again, we want this `find_vtable_types_for_unsizing()` to provide the pair
/// `(SomeStruct, SomeTrait)`.
///
/// Finally, there is also the case of custom unsizing coercions, e.g. for
/// smart pointers such as `Rc` and `Arc`.
fn find_vtable_types_for_unsizing<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                            source_ty: ty::Ty<'tcx>,
                                            target_ty: ty::Ty<'tcx>)
                                            -> (ty::Ty<'tcx>, ty::Ty<'tcx>) {
    match (&source_ty.sty, &target_ty.sty) {
        (&ty::TyBox(a), &ty::TyBox(b)) |
        (&ty::TyRef(_, ty::TypeAndMut { ty: a, .. }),
         &ty::TyRef(_, ty::TypeAndMut { ty: b, .. })) |
        (&ty::TyRef(_, ty::TypeAndMut { ty: a, .. }),
         &ty::TyRawPtr(ty::TypeAndMut { ty: b, .. })) |
        (&ty::TyRawPtr(ty::TypeAndMut { ty: a, .. }),
         &ty::TyRawPtr(ty::TypeAndMut { ty: b, .. })) => {
            let (inner_source, inner_target) = (a, b);

            if !type_is_sized(scx.tcx(), inner_source) {
                (inner_source, inner_target)
            } else {
                scx.tcx().struct_lockstep_tails(inner_source, inner_target)
            }
        }

        (&ty::TyAdt(source_adt_def, source_substs),
         &ty::TyAdt(target_adt_def, target_substs)) => {
            assert_eq!(source_adt_def, target_adt_def);

            let kind = custom_coerce_unsize_info(scx, source_ty, target_ty);

            let coerce_index = match kind {
                CustomCoerceUnsized::Struct(i) => i
            };

            let source_fields = &source_adt_def.struct_variant().fields;
            let target_fields = &target_adt_def.struct_variant().fields;

            assert!(coerce_index < source_fields.len() &&
                    source_fields.len() == target_fields.len());

            find_vtable_types_for_unsizing(scx,
                                           source_fields[coerce_index].ty(scx.tcx(),
                                                                          source_substs),
                                           target_fields[coerce_index].ty(scx.tcx(),
                                                                          target_substs))
        }
        _ => bug!("find_vtable_types_for_unsizing: invalid coercion {:?} -> {:?}",
                  source_ty,
                  target_ty)
    }
}

fn create_fn_trans_item<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                  def_id: DefId,
                                  fn_substs: &'tcx Substs<'tcx>,
                                  param_substs: &'tcx Substs<'tcx>)
                                  -> TransItem<'tcx> {
    let tcx = scx.tcx();

    debug!("create_fn_trans_item(def_id={}, fn_substs={:?}, param_substs={:?})",
            def_id_to_string(tcx, def_id),
            fn_substs,
            param_substs);

    // We only get here, if fn_def_id either designates a local item or
    // an inlineable external item. Non-inlineable external items are
    // ignored because we don't want to generate any code for them.
    let concrete_substs = monomorphize::apply_param_substs(scx,
                                                           param_substs,
                                                           &fn_substs);
    assert!(concrete_substs.is_normalized_for_trans(),
            "concrete_substs not normalized for trans: {:?}",
            concrete_substs);
    TransItem::Fn(Instance::new(def_id, concrete_substs))
}

/// Creates a `TransItem` for each method that is referenced by the vtable for
/// the given trait/impl pair.
fn create_trans_items_for_vtable_methods<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                                   trait_ty: ty::Ty<'tcx>,
                                                   impl_ty: ty::Ty<'tcx>,
                                                   output: &mut Vec<TransItem<'tcx>>) {
    assert!(!trait_ty.needs_subst() && !impl_ty.needs_subst());

    if let ty::TyDynamic(ref trait_ty, ..) = trait_ty.sty {
        if let Some(principal) = trait_ty.principal() {
            let poly_trait_ref = principal.with_self_ty(scx.tcx(), impl_ty);
            let param_substs = scx.tcx().intern_substs(&[]);

            // Walk all methods of the trait, including those of its supertraits
            let methods = traits::get_vtable_methods(scx.tcx(), poly_trait_ref);
            let methods = methods.filter_map(|method| method)
                .filter_map(|(def_id, substs)| do_static_dispatch(scx, def_id, substs,
                                                                  param_substs))
                .filter(|&(def_id, _)| can_have_local_instance(scx.tcx(), def_id))
                .map(|(def_id, substs)| create_fn_trans_item(scx, def_id, substs, param_substs));
            output.extend(methods);
        }
    }
}

/// Is the type's representation size known at compile time?
pub fn type_is_sized<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, ty: Ty<'tcx>) -> bool {
    ty.is_sized(tcx, &tcx.empty_parameter_environment(), DUMMY_SP)
}

fn do_static_dispatch<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                fn_def_id: DefId,
                                fn_substs: &'tcx Substs<'tcx>,
                                param_substs: &'tcx Substs<'tcx>)
                                -> Option<(DefId, &'tcx Substs<'tcx>)> {
    debug!("do_static_dispatch(fn_def_id={}, fn_substs={:?}, param_substs={:?})",
           def_id_to_string(scx.tcx(), fn_def_id),
           fn_substs,
           param_substs);

    if let Some(trait_def_id) = scx.tcx().trait_of_item(fn_def_id) {
        debug!(" => trait method, attempting to find impl");
        do_static_trait_method_dispatch(scx,
                                        &scx.tcx().associated_item(fn_def_id),
                                        trait_def_id,
                                        fn_substs,
                                        param_substs)
    } else {
        debug!(" => regular function");
        // The function is not part of an impl or trait, no dispatching
        // to be done
        Some((fn_def_id, fn_substs))
    }
}

// Given a trait-method and substitution information, find out the actual
// implementation of the trait method.
fn do_static_trait_method_dispatch<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                             trait_method: &ty::AssociatedItem,
                                             trait_id: DefId,
                                             callee_substs: &'tcx Substs<'tcx>,
                                             param_substs: &'tcx Substs<'tcx>)
                                             -> Option<(DefId, &'tcx Substs<'tcx>)> {
    let tcx = scx.tcx();
    debug!("do_static_trait_method_dispatch(trait_method={}, \
                                            trait_id={}, \
                                            callee_substs={:?}, \
                                            param_substs={:?}",
           def_id_to_string(scx.tcx(), trait_method.def_id),
           def_id_to_string(scx.tcx(), trait_id),
           callee_substs,
           param_substs);

    let rcvr_substs = monomorphize::apply_param_substs(scx,
                                                       param_substs,
                                                       &callee_substs);
    let trait_ref = ty::TraitRef::from_method(tcx, trait_id, rcvr_substs);
    let vtbl = fulfill_obligation(scx, DUMMY_SP, ty::Binder(trait_ref));

    // Now that we know which impl is being used, we can dispatch to
    // the actual function:
    match vtbl {
        traits::VtableImpl(impl_data) => {
            Some(traits::find_method(tcx, trait_method.name, rcvr_substs, &impl_data))
        }
        traits::VtableClosure(closure_data) => {
            Some((closure_data.closure_def_id, closure_data.substs.substs))
        }
        // Trait object and function pointer shims are always
        // instantiated in-place, and as they are just an ABI-adjusting
        // indirect call they do not have any dependencies.
        traits::VtableFnPointer(..) |
        traits::VtableObject(..) => {
            None
        }
        _ => {
            bug!("static call to invalid vtable: {:?}", vtbl)
        }
    }
}

struct MirNeighborCollector<'a, 'tcx: 'a> {
    scx: &'a SharedCrateContext<'a, 'tcx>,
    mir: &'a mir::Mir<'tcx>,
    output: &'a mut Vec<TransItem<'tcx>>,
    param_substs: &'tcx Substs<'tcx>
}

impl<'a, 'tcx> MirVisitor<'tcx> for MirNeighborCollector<'a, 'tcx> {

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        debug!("visiting rvalue {:?}", *rvalue);

        match *rvalue {
            // When doing an cast from a regular pointer to a fat pointer, we
            // have to instantiate all methods of the trait being cast to, so we
            // can build the appropriate vtable.
            mir::Rvalue::Cast(mir::CastKind::Unsize, ref operand, target_ty) => {
                let target_ty = monomorphize::apply_param_substs(self.scx,
                                                                 self.param_substs,
                                                                 &target_ty);
                let source_ty = operand.ty(self.mir, self.scx.tcx());
                let source_ty = monomorphize::apply_param_substs(self.scx,
                                                                 self.param_substs,
                                                                 &source_ty);
                let (source_ty, target_ty) = find_vtable_types_for_unsizing(self.scx,
                                                                            source_ty,
                                                                            target_ty);
                // This could also be a different Unsize instruction, like
                // from a fixed sized array to a slice. But we are only
                // interested in things that produce a vtable.
                if target_ty.is_trait() && !source_ty.is_trait() {
                    create_trans_items_for_vtable_methods(self.scx,
                                                          target_ty,
                                                          source_ty,
                                                          self.output);
                }
            }
            _ => { /* not interesting */ }
        }

        self.super_rvalue(rvalue, location);
    }

    fn visit_lvalue(&mut self,
                    lvalue: &mir::Lvalue<'tcx>,
                    context: mir_visit::LvalueContext<'tcx>,
                    location: Location) {
        debug!("visiting lvalue {:?}", *lvalue);
        self.super_lvalue(lvalue, context, location);
    }

    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: Location) {
        debug!("visiting operand {:?}", *operand);

        let callee = match *operand {
            mir::Operand::Constant(ref constant) => {
                if let ty::TyFnDef(def_id, substs, _) = constant.ty.sty {
                    // This is something that can act as a callee, proceed
                    Some((def_id, substs))
                } else {
                    // This is not a callee, but we still have to look for
                    // references to `const` items
                    if let mir::Literal::Item { def_id, substs } = constant.literal {
                        let tcx = self.scx.tcx();
                        let substs = monomorphize::apply_param_substs(self.scx,
                                                                      self.param_substs,
                                                                      &substs);

                        // If the constant referred to here is an associated
                        // item of a trait, we need to resolve it to the actual
                        // constant in the corresponding impl. Luckily
                        // const_eval::lookup_const_by_id() does that for us.
                        if let Some((expr, _)) = const_eval::lookup_const_by_id(tcx,
                                                                                def_id,
                                                                                Some(substs)) {
                            // The hir::Expr we get here is the initializer of
                            // the constant, what we really want is the item
                            // DefId.
                            let const_node_id = tcx.map.get_parent(expr.id);
                            let def_id = if tcx.map.is_inlined_node_id(const_node_id) {
                                tcx.sess.cstore.defid_for_inlined_node(const_node_id).unwrap()
                            } else {
                                tcx.map.local_def_id(const_node_id)
                            };

                            collect_const_item_neighbours(self.scx,
                                                          def_id,
                                                          substs,
                                                          self.output);
                        }
                    }

                    None
                }
            }
            _ => None
        };

        if let Some((callee_def_id, callee_substs)) = callee {
            debug!(" => operand is callable");

            // `callee_def_id` might refer to a trait method instead of a
            // concrete implementation, so we have to find the actual
            // implementation. For example, the call might look like
            //
            // std::cmp::partial_cmp(0i32, 1i32)
            //
            // Calling do_static_dispatch() here will map the def_id of
            // `std::cmp::partial_cmp` to the def_id of `i32::partial_cmp<i32>`
            let dispatched = do_static_dispatch(self.scx,
                                                callee_def_id,
                                                callee_substs,
                                                self.param_substs);

            if let Some((callee_def_id, callee_substs)) = dispatched {
                // if we have a concrete impl (which we might not have
                // in the case of something compiler generated like an
                // object shim or a closure that is handled differently),
                // we check if the callee is something that will actually
                // result in a translation item ...
                if can_result_in_trans_item(self.scx.tcx(), callee_def_id) {
                    // ... and create one if it does.
                    let trans_item = create_fn_trans_item(self.scx,
                                                          callee_def_id,
                                                          callee_substs,
                                                          self.param_substs);
                    self.output.push(trans_item);
                }
            }
        }

        self.super_operand(operand, location);

        fn can_result_in_trans_item<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                              def_id: DefId)
                                              -> bool {
            match tcx.item_type(def_id).sty {
                ty::TyFnDef(def_id, _, f) => {
                    // Some constructors also have type TyFnDef but they are
                    // always instantiated inline and don't result in
                    // translation item. Same for FFI functions.
                    if let Some(hir_map::NodeForeignItem(_)) = tcx.map.get_if_local(def_id) {
                        return false;
                    }

                    if let Some(adt_def) = f.sig.output().skip_binder().ty_adt_def() {
                        if adt_def.variants.iter().any(|v| def_id == v.did) {
                            return false;
                        }
                    }
                }
                ty::TyClosure(..) => {}
                _ => return false
            }

            can_have_local_instance(tcx, def_id)
        }
    }

    fn visit_terminator_kind(&mut self,
                             block: mir::BasicBlock,
                             kind: &mir::TerminatorKind<'tcx>,
                             location: Location) {
        self.super_terminator_kind(block, kind, location);
    }
}

struct RootCollector<'b, 'a: 'b, 'tcx: 'a + 'b> {
    scx: &'b SharedCrateContext<'a, 'tcx>,
    output: &'b mut Vec<TransItem<'tcx>>,
}

impl<'b, 'a, 'v> ItemLikeVisitor<'v> for RootCollector<'b, 'a, 'v> {
    fn visit_item(&mut self, item: &'v hir::Item) {
        match item.node {
            hir::ItemExternCrate(..) |
            hir::ItemUse(..)         |
            hir::ItemForeignMod(..)  |
            hir::ItemTy(..)          |
            hir::ItemDefaultImpl(..) |
            hir::ItemTrait(..)       |
            hir::ItemImpl(..)        |
            hir::ItemEnum(..)        |
            hir::ItemStruct(..)      |
            hir::ItemUnion(..)       |
            hir::ItemMod(..)         => {
                // Nothing to do, just keep recursing...
            }

            hir::ItemStatic(..) => {
                debug!("RootCollector: ItemStatic({})",
                       def_id_to_string(self.scx.tcx(),
                                        self.scx.tcx().map.local_def_id(item.id)));
                self.output.push(TransItem::Static(item.id));
            }
            hir::ItemConst(..) => {
                // const items only generate translation items if they are
                // actually used somewhere. Just declaring them is insufficient.
            }
            hir::ItemFn(.., ref generics, _) => {
                if !generics.is_type_parameterized() {
                    let def_id = self.scx.tcx().map.local_def_id(item.id);

                    debug!("RootCollector: ItemFn({})",
                           def_id_to_string(self.scx.tcx(), def_id));

                    let instance = Instance::mono(self.scx, def_id);
                    self.output.push(TransItem::Fn(instance));
                }
            }
        }
    }

    fn visit_impl_item(&mut self, ii: &'v hir::ImplItem) {
    }
}

fn check_type_length_limit<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                     instance: Instance<'tcx>)
{
    let type_length = instance.substs.types().flat_map(|ty| ty.walk()).count();
    debug!(" => type length={}", type_length);

    // Rust code can easily create exponentially-long types using only a
    // polynomial recursion depth. Even with the default recursion
    // depth, you can easily get cases that take >2^60 steps to run,
    // which means that rustc basically hangs.
    //
    // Bail out in these cases to avoid that bad user experience.
    let type_length_limit = tcx.sess.type_length_limit.get();
    if type_length > type_length_limit {
        // The instance name is already known to be too long for rustc. Use
        // `{:.64}` to avoid blasting the user's terminal with thousands of
        // lines of type-name.
        let instance_name = instance.to_string();
        let msg = format!("reached the type-length limit while instantiating `{:.64}...`",
                          instance_name);
        let mut diag = if let Some(node_id) = tcx.map.as_local_node_id(instance.def) {
            tcx.sess.struct_span_fatal(tcx.map.span(node_id), &msg)
        } else {
            tcx.sess.struct_fatal(&msg)
        };

        diag.note(&format!(
            "consider adding a `#![type_length_limit=\"{}\"]` attribute to your crate",
            type_length_limit*2));
        diag.emit();
        tcx.sess.abort_if_errors();
    }
}

fn check_recursion_limit<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                   instance: Instance<'tcx>,
                                   recursion_depths: &mut DefIdMap<usize>)
                                   -> (DefId, usize) {
    let recursion_depth = recursion_depths.get(&instance.def)
                                          .map(|x| *x)
                                          .unwrap_or(0);
    debug!(" => recursion depth={}", recursion_depth);

    // Code that needs to instantiate the same function recursively
    // more than the recursion limit is assumed to be causing an
    // infinite expansion.
    if recursion_depth > tcx.sess.recursion_limit.get() {
        let error = format!("reached the recursion limit while instantiating `{}`",
                            instance);
        if let Some(node_id) = tcx.map.as_local_node_id(instance.def) {
            tcx.sess.span_fatal(tcx.map.span(node_id), &error);
        } else {
            tcx.sess.fatal(&error);
        }
    }

    recursion_depths.insert(instance.def, recursion_depth + 1);

    (instance.def, recursion_depth)
}

fn can_have_local_instance<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                     def_id: DefId)
                                     -> bool {
    tcx.sess.cstore.can_have_local_instance(tcx, def_id)
}

fn visit_mir_and_promoted<'tcx, V: MirVisitor<'tcx>>(mut visitor: V, mir: &mir::Mir<'tcx>) {
    visitor.visit_mir(&mir);
    for promoted in &mir.promoted {
        visitor.visit_mir(promoted);
    }
}

fn def_id_to_string<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                              def_id: DefId)
                              -> String {
    let mut output = String::new();
    let printer = DefPathBasedNames::new(tcx, false, false);
    printer.push_def_path(def_id, &mut output);
    output
}
