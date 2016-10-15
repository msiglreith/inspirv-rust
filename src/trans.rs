
use rustc_mir as mir;
use rustc::mir::transform::MirSource;
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal::*;
use rustc_const_math::{ConstInt, ConstFloat};
use rustc::ty::{self, TyCtxt, Ty};
use rustc::hir;
use rustc::hir::def::CtorKind;
use rustc::hir::def_id::DefId;
use rustc::util::common::time;
use rustc_borrowck as borrowck;
use rustc_data_structures::indexed_vec::{Idx, IndexVec};
use rustc::ty::subst::Substs;
use syntax::ast::{NodeId, IntTy, UintTy, FloatTy};
use std::ops::Deref;
use std::collections::HashMap;
use inspirv::instruction;
use inspirv::types::*;
use inspirv::core::instruction::*;
use inspirv::core::enumeration::*;
use inspirv::instruction::BranchInstruction;
use inspirv_builder;
use inspirv_builder::function::{Argument, LocalVar, Block, FuncId};
use inspirv_builder::module::{self, Type, RawModule, ModuleBuilder, ConstValue, ConstValueFloat};
use attribute::{self, Attribute};
use monomorphize;
use traits;
use error::PResult;

// const SOURCE_INSPIRV_RUST: u32 = 0xCC; // TODO: might get an official number in the future?
const VERSION_INSPIRV_RUST: u32 = 0x00010000; // |major(1 byte)|minor(1 byte)|patch(2 byte)|

pub fn translate_to_spirv<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>,
                                    mut mir_map: &mut MirMap<'tcx>,
                                    analysis: &ty::CrateAnalysis) -> Option<RawModule> {
    let time_passes = tcx.sess.time_passes();

    // Run the passes that transform the MIR into a more suitable for translation
    time(time_passes, "Prepare MIR codegen passes", || {
        let mut passes = ::rustc::mir::transform::Passes::new();
        passes.push_hook(box mir::transform::dump_mir::DumpMir);
        passes.push_pass(box mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box mir::transform::simplify_cfg::SimplifyCfg::new("no-landing-pads"));

        passes.push_pass(box mir::transform::erase_regions::EraseRegions);

        passes.push_pass(box mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box borrowck::ElaborateDrops);
        passes.push_pass(box mir::transform::no_landing_pads::NoLandingPads);
        passes.push_pass(box mir::transform::simplify_cfg::SimplifyCfg::new("elaborate-drops"));

        passes.push_pass(box mir::transform::deaggregator::Deaggregator);

        passes.push_pass(box mir::transform::add_call_guards::AddCallGuards);
        passes.push_pass(box mir::transform::dump_mir::Marker("PreTrans"));

        passes.run_passes(*tcx, &mut mir_map);
    });

    time(time_passes,
         "translation",
         move || trans_crate(tcx, mir_map, analysis))
}

fn trans_crate<'a, 'tcx>(tcx: &TyCtxt<'a, 'tcx, 'tcx>,
                         mir_map: &MirMap<'tcx>,
                         _analysis: &ty::CrateAnalysis) -> Option<RawModule> {
    let mut builder = ModuleBuilder::new();
    builder.with_source(SourceLanguage::SourceLanguageUnknown, VERSION_INSPIRV_RUST);

    let mut v = InspirvModuleCtxt {
        tcx: tcx,
        mir_map: mir_map,
        builder: builder,

        fn_ids: HashMap::new(),
    };

    v.trans()
}

#[derive(Clone, Debug)]
pub enum SpirvType {
    NoRef(Type),
    Ref {
        ty: Type,
        mutable: bool,
        // Keeping track of the original object, we are refering to
        referent: Option<Id>,
    },
}

impl SpirvType {
    fn is_ref(&self) -> bool {
        if let SpirvType::Ref {..} = *self {
            true
        } else {
            false
        }
    }

    fn ty(&self) -> &Type {
        use self::SpirvType::*;
        match *self {
            NoRef(ref ty)
            | Ref{ ref ty, .. } => ty,
        }
    }
}

impl Into<Type> for SpirvType {
    fn into(self) -> Type {
        use self::SpirvType::*;
        match self {
            NoRef(ty)
            | Ref{ ty, .. } => ty,
        }
    }
}

impl Deref for SpirvType {
    type Target = Type;
    fn deref(&self) -> &Self::Target {
        use self::SpirvType::*;
        match *self {
            NoRef(ref ty)
            | Ref{ ref ty, .. } => ty,
        }
    }
}

pub type IdAndType = (Id, SpirvType);

#[derive(Clone, Debug)]
pub enum SpirvOperand<'tcx> {
    Consume(SpirvLvalue),
    Constant(Id, SpirvType),
    FnCall(DefId, &'tcx Substs<'tcx>),
    None, // TODO: temp
}

impl<'tcx> SpirvOperand<'tcx> {
    pub fn is_constant(&self) -> bool {
        match *self {
            SpirvOperand::Constant(..) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum SpirvLvalue {
    // Standard variables, can be temporary or named variables, etc.
    Variable(Id, SpirvType, StorageClass),

    // struct objects passed to functions, e.g. interfaces
    SignatureStruct(Vec<(Id, Type)>, StorageClass),

    // chain of field access e.g a.b.c.d
    AccessChain(Id, StorageClass, Vec<Id>, Type),

    // Return variable handled specially as SPIR-V differs between OpReturn and OpReturnVariable
    Return(IdAndType),

    // Ignore this lvalue, e.g. return = ()
    Ignore,
}

#[derive(Clone, Debug)]
pub enum FuncArg {
    Argument(IdAndType),
    Interface(Vec<(Id, Type)>),
    ConstBuffer(IdAndType),
}

#[derive(Clone)]
pub enum FuncReturn {
    Return(IdAndType),
    Interface(Vec<(Id, Type)>),
}

pub struct InspirvModuleCtxt<'v, 'tcx: 'v> {
    tcx: &'v TyCtxt<'v, 'tcx, 'tcx>,
    mir_map: &'v MirMap<'tcx>,
    builder: ModuleBuilder,

    // Save id's of all functions
    fn_ids: HashMap<(DefId, ty::FnSig<'tcx>), FuncId>,
}

pub struct InspirvFnCtxt<'v, 'tcx: 'v> {
    tcx: &'v TyCtxt<'v, 'tcx, 'tcx>,
    mir_map: &'v MirMap<'tcx>,
    mir: &'v Mir<'tcx>,
    def_id: DefId,
    node_id: NodeId,
    pub builder: &'v mut ModuleBuilder,

    fn_ids: &'v mut HashMap<(DefId, ty::FnSig<'tcx>), FuncId>,
    substs: Option<&'v Substs<'tcx>>,

    arg_ids: IndexVec<Local, Option<FuncArg>>,
    local_ids: IndexVec<Local, Option<IdAndType>>,
    return_ids: Option<FuncReturn>,
}

#[derive(PartialEq, Eq)]
enum FnTrans {
    OnlyPublic,
    Required,
}

impl<'v, 'tcx> InspirvModuleCtxt<'v, 'tcx> {
    fn trans(&mut self) -> Option<RawModule> {
        let def_ids = self.mir_map.map.keys();
        for def_id in def_ids {
            let mir = self.mir_map.map.get(&def_id).unwrap();
            let id = self.tcx.map.as_local_node_id(def_id).unwrap();
            let src = MirSource::from_node(*self.tcx, id);

            let mut fn_ctxt = InspirvFnCtxt {
                tcx: self.tcx,
                mir_map: self.mir_map,
                mir: mir,
                def_id: def_id,
                node_id: id,
                builder: &mut self.builder,
                fn_ids: &mut self.fn_ids,
                substs: None,

                arg_ids: IndexVec::new(),
                local_ids: IndexVec::new(),
                return_ids: None,
            };

            let result = match src {
                MirSource::Const(_) => fn_ctxt.trans_const(),
                MirSource::Fn(_) => fn_ctxt.trans_fn(FnTrans::OnlyPublic),
                MirSource::Static(_, mutability) => fn_ctxt.trans_static(mutability),
                MirSource::Promoted(_, promoted) => {
                    println!("{:?}", (id, promoted, mir));
                    Ok(())
                }
            };

            match result {
                Ok(_) => {}
                Err(mut err) => {
                    err.emit();
                    return None;
                }
            }
        }

        match self.builder.build() {
            Ok(module) => Some(module),
            Err(err) => {
                println!("{:?}", err);
                None
            }
        }
    }
}

impl<'e, 'v: 'e, 'tcx> InspirvFnCtxt<'v, 'tcx> {
    fn trans_static(&'e mut self, mutability: hir::Mutability) -> PResult<'e, ()> {
        println!("{:?}", (self.node_id, mutability, self.mir));
        Ok(())
    }

    fn trans_const(&'e mut self) -> PResult<'e, ()> {
        self.arg_ids = IndexVec::new();

        let const_name = &*self.tcx.map.name(self.node_id).as_str();
        let mut const_fn = self.builder.define_function_named(const_name);

        let return_ty = self.rust_ty_to_spirv_ref(self.mir.return_ty)?;
        if return_ty.is_ref() {
            return Err(self.tcx.sess.struct_err("Inspirv: References as return type are currently unsupported"));
        }
        self.return_ids = if let Type::Void = *return_ty.ty() {
            None
        } else {
            let id = self.builder.alloc_id();
            let local_var = LocalVar {
                id: id,
                ty: return_ty.clone().into(),
            };
            const_fn.variables.push(local_var);
            Some(FuncReturn::Return((id, return_ty.clone())))
        };

        const_fn.ret_ty = return_ty.into();

        println!("{:?} {:?}", self.node_id, self.mir);

        self.trans(const_fn)
    }

    fn trans_fn(&'e mut self, translation_mode: FnTrans) -> PResult<'e, ()> {
        let did = self.def_id;
        let type_scheme = self.tcx.lookup_item_type(did);

        // Don't translate generic functions!
        if self.substs.is_none() && (!type_scheme.generics.types.is_empty() || type_scheme.generics.parent_types > 0) {
            return Ok(());
        }
        
        let signature = {
            let sig = type_scheme.ty.fn_sig().skip_binder();
            if let Some(substs) = self.substs {
                monomorphize::apply_param_substs(self.tcx, substs, sig)
            } else {
                sig.clone()
            }
        };

        // Check if already translate (e.g. instance of a generic)
        if self.fn_ids.contains_key(&(did, signature.clone())) {
            return Ok(());
        }

        self.arg_ids = IndexVec::new();
        let fn_module = {
            let attrs = attribute::parse(self.tcx.sess, self.tcx.map.attrs(self.node_id))?;

            // We don't translate builtin functions, these will be handled internally
            if attrs.iter().any(|attr| match *attr {
                Attribute::CompilerBuiltin | Attribute::Intrinsic(..) => true,
                _ => false
            }) {
                return Ok(());
            }

            let fn_name = &*self.tcx.map.name(self.node_id).as_str();

            // check if we have an entry point
            let entry_point = attrs.iter().find(|attr| match **attr {
                Attribute::EntryPoint { .. } => true,
                _ => false,
            });

            // only translate exported functions if requested to keep the resulting SPIR-V small
            if translation_mode == FnTrans::OnlyPublic && entry_point.is_none() {
                return Ok(());
            }

            let mut interface_ids = Vec::new(); // entry points
            let mut params = Vec::new(); // `normal` function

            let mut err = None;

            // Extract all arguments and store their ids in a list for faster access later
            // Arguments as Input interface if the structs have to corresponding annotations
            for (i, arg) in self.mir.local_decls.iter().enumerate() {
                // check for parameter range
                if i == 0 {
                    continue;
                } else if i > self.mir.arg_count {
                    break;
                }

                let name = arg.name.map(|name| (&*name.as_str()).to_owned()).unwrap_or("_".to_owned());

                if let Some(ty_id) = arg.ty.ty_to_def_id() {
                    let attrs = self.get_node_attributes(ty_id)?;
                    let interface = attrs.iter().any(|attr| match *attr {
                            Attribute::Interface => true,
                            _ => false,
                        });
                    let const_buffer = attrs.iter().any(|attr| match *attr {
                            Attribute::ConstBuffer => true,
                            _ => false,
                        });

                    if interface {
                        if let ty::TyAdt(adt, subs) = arg.ty.sty {
                            // unwrap wrapper type!
                            let struct_ty = adt.struct_variant().fields[0].ty(*self.tcx, subs);
                            if let ty::TyAdt(adt, subs) = struct_ty.sty {
                                let struct_ty_id = struct_ty.ty_to_def_id().unwrap();
                                let interfaces = adt.struct_variant().fields.iter().map(|field| {
                                    let ty = self.rust_ty_to_spirv(field.ty(*self.tcx, subs))?;
                                    let node_id = self.get_node_id(struct_ty_id);
                                    let name = format!("{}_{}", self.tcx.map.name(node_id), field.name.as_str());
                                    let id = self.builder.define_variable(name.as_str(), ty.clone(),
                                                                 StorageClass::StorageClassInput);

                                    // HELP! A nicer way to get the attributes?
                                    // Get struct field attributes
                                    let node = self.tcx.map.get(node_id);
                                    let field_id = self.tcx.map.as_local_node_id(field.did).unwrap();
                                    let field_attrs = {
                                        if let hir::map::Node::NodeItem(item) = node {
                                            if let hir::Item_::ItemStruct(ref variant_data, _) = item.node {
                                                let field = variant_data.fields().iter()
                                                                        .find(|field| field.id == field_id)
                                                                        .expect("Unable to find struct field by id");
                                                attribute::parse(self.tcx.sess, &*field.attrs)?
                                            } else {
                                                bug!("Struct item node should be a struct {:?}", item.node)
                                            }
                                        } else {
                                            bug!("Struct node should be a NodeItem {:?}", node)
                                        }
                                    };

                                    for attr in field_attrs {
                                        match attr {
                                            Attribute::Location { location } => {
                                                self.builder.add_decoration(id, Decoration::DecorationLocation(LiteralInteger(location as u32)));
                                            }
                                            // Rust doesn't allow attributes associated with `type foo = bar` /:
                                            Attribute::Builtin { builtin } => {
                                                // TODO: check if our decorations follow Vulkan specs e.g. Position only for float4
                                                self.builder.add_decoration(id, Decoration::DecorationBuiltIn(builtin));
                                            }
                                            _ => ()
                                        }
                                    }

                                    interface_ids.push(id);
                                    Ok((id, ty))
                                }).collect::<PResult<Vec<_>>>()?;

                                self.arg_ids.push(Some(FuncArg::Interface(interfaces)));
                            } else {
                                err = Some(self.tcx.sess.struct_err("Input argument inner type needs to be a struct type"));
                            }
                        } else {
                            err = Some(self.tcx.sess.struct_err("Input argument inner type needs to be a struct type"));
                        }
                    } else if const_buffer {
                        if let ty::TyAdt(adt, subs) = arg.ty.sty {
                            // unwrap wrapper type!
                            let struct_ty = adt.struct_variant().fields[0].ty(*self.tcx, subs);
                            let struct_ty_id = struct_ty.ty_to_def_id().unwrap();
                            if let ty::TyAdt(adt, _subs) = struct_ty.sty {
                                let ty = self.rust_ty_to_spirv(struct_ty)?;
                                let node_id = self.get_node_id(struct_ty_id);
                                let ty_id = self.builder.define_named_type(&ty, &*self.tcx.map.name(node_id).as_str());
                                let id = self.builder.define_variable(&*name, ty.clone(), StorageClass::StorageClassUniform);  
                                self.arg_ids.push(Some(FuncArg::ConstBuffer((id, SpirvType::NoRef(ty.clone())))));

                                self.builder.add_decoration(ty_id, Decoration::DecorationBlock);
                                for (member, field) in adt.struct_variant().fields.iter().enumerate() {
                                    self.builder.name_id_member(ty_id, member as u32, &*field.name.as_str());
                                }

                                let fields = if let Type::Struct(fields) = ty { fields } else { bug!("cbuffer not a struct!") };
                                let mut offset = 0;
                                for (member, field) in fields.iter().enumerate() {
                                    let unalignment = offset % field.alignment();
                                    if unalignment != 0 {
                                        offset += field.alignment() - unalignment;
                                    }

                                    self.builder.add_decoration_member(ty_id, member as u32, Decoration::DecorationOffset(LiteralInteger(offset as u32)));
                                    offset += field.size_of();

                                    // Matrix types require ColMajor/RowMajor decorations and MatrixStride [SPIR-V 2.16.2]
                                    if let Type::Matrix { ref base, rows, cols } = *field {
                                        let stride = Type::Vector { base: base.clone(), components: rows }.size_of();
                                        self.builder.add_decoration_member(ty_id, member as u32, Decoration::DecorationMatrixStride(LiteralInteger(stride as u32)));
                                        self.builder.add_decoration_member(ty_id, member as u32, Decoration::DecorationColMajor);
                                    }
                                }

                                let attrs = attribute::parse(self.tcx.sess, self.tcx.map.attrs(node_id))?;

                                for attr in attrs {
                                    if let Attribute::Descriptor { set, binding } = attr {
                                        self.builder.add_decoration(id, Decoration::DecorationDescriptorSet(LiteralInteger(set as u32)));
                                        self.builder.add_decoration(id, Decoration::DecorationBinding(LiteralInteger(binding as u32)));
                                    }
                                }
                            } else {
                                err = Some(self.tcx.sess.struct_err("Const buffer argument inner type requires to be struct type"));
                            }
                        } else {
                            err = Some(self.tcx.sess.struct_err("Const buffer argument type requires to be struct type"));
                        }
                    } else if entry_point.is_some() {
                        // Entrypoint functions don't have actual input/output parameters
                        // We use them for the shader interface and const buffers
                        err = Some(self.tcx.sess.struct_err("Input argument type requires interface or cbuffer attribute"));
                    } else {
                        let id = self.builder.alloc_id();
                        let ty = self.rust_ty_to_spirv_ref(arg.ty)?;
                        let arg = Argument {
                            id: id,
                            ty: ty.clone().into(),
                        };
                        params.push(arg);
                        self.builder.name_id(id, &*name); // TODO: hide this behind a function module interface
                        self.arg_ids.push(Some(FuncArg::Argument((id, ty))));
                    }
                } else if entry_point.is_some() {
                    err = Some(self.tcx.sess.struct_err("Argument type not defined in local crate"));
                } else {
                    //
                    let id = self.builder.alloc_id();
                    let ty = self.rust_ty_to_spirv_ref(arg.ty)?;
                    let arg = Argument {
                        id: id,
                        ty: ty.clone().into(),
                    };
                    params.push(arg);
                    self.builder.name_id(id, &*name); // TODO: hide this behind a function module interface
                    self.arg_ids.push(Some(FuncArg::Argument((id, ty))));
                }

                if let Some(mut err) = err {
                    if let Some(source) = arg.source_info { err.set_span(source.span); }
                    else { err.set_span(self.mir.span); }
                    return Err(err)
                }             
            }

            // Return type and function creation
            //
            // Entry Point Handling:
            //  These functions don't have actual input/output parameters
            //  We use them for the shader interface and uniforms
            let ref return_ptr = self.mir.local_decls[Local::new(0)];
            let mut err = None;
            let func = if let Some(&Attribute::EntryPoint{ stage, ref execution_modes }) = entry_point {
                match self.mir.return_ty.sty {
                    ty::TyAdt(adt, subs) => {
                        if let Some(ty_id) = self.mir.return_ty.ty_to_def_id() {
                            let interfaces = adt.struct_variant().fields.iter().map(|field| {
                                let ty = self.rust_ty_to_spirv(field.ty(*self.tcx, subs))?;
                                let node_id = self.get_node_id(ty_id);
                                let name = format!("{}_{}", self.tcx.map.name(node_id), field.name.as_str());
                                let id = self.builder.define_variable(name.as_str(), ty.clone(),
                                                             StorageClass::StorageClassOutput);

                                // HELP! A nicer way to get the attributes?
                                // Get struct field attributes
                                let node = self.tcx.map.get(node_id);
                                let field_id = self.tcx.map.as_local_node_id(field.did).unwrap();
                                let field_attrs = {
                                    if let hir::map::Node::NodeItem(item) = node {
                                        if let hir::Item_::ItemStruct(ref variant_data, _) = item.node {
                                            let field = variant_data.fields().iter()
                                                                    .find(|field| field.id == field_id)
                                                                    .expect("Unable to find struct field by id");
                                            attribute::parse(self.tcx.sess, &*field.attrs)?
                                        } else {
                                            bug!("Struct item node should be a struct {:?}", item.node)
                                        }
                                    } else {
                                        bug!("Struct node should be a NodeItem {:?}", node)
                                    }
                                };

                                let mut attribute_loc = None;

                                for attr in field_attrs {
                                    match attr {
                                        Attribute::Location { location } => { attribute_loc = Some(location); }
                                        // Rust doesn't allow attributes associated with `type foo = bar` /:
                                        Attribute::Builtin { builtin } => {
                                            // TODO: check if our decorations follow Vulkan specs e.g. Position only for float4
                                            self.builder.add_decoration(id, Decoration::DecorationBuiltIn(builtin));
                                        }
                                        _ => ()
                                    }
                                }

                                if let Some(location) = attribute_loc {
                                    self.builder.add_decoration(id, Decoration::DecorationLocation(LiteralInteger(location as u32)));
                                } else {
                                    err = Some(self.tcx.sess.struct_err("Output argument type field requires a location attribute"));
                                }

                                interface_ids.push(id);
                                Ok((id, ty))
                            }).collect::<PResult<Vec<_>>>()?;
                            self.return_ids = Some(FuncReturn::Interface(interfaces));
                        } else {
                            err = Some(self.tcx.sess.struct_err("Output argument type not defined in local crate"));
                        }
                    }
                    ty::TyTuple(tys) if tys.is_empty() => self.return_ids = None, // MIR doesn't use void(!) instead the () type for some reason \o/
                    _ => { err = Some(self.tcx.sess.struct_err("Output argument type requires to be a struct type or empty")); }
                }

                //
                let mut execution_modes = execution_modes.clone();
                if stage == ExecutionModel::ExecutionModelFragment {
                    execution_modes.insert(ExecutionModeKind::ExecutionModeOriginUpperLeft, ExecutionMode::ExecutionModeOriginUpperLeft);
                }

                // Define entry point in SPIR-V
                let mut func = self.builder
                    .define_entry_point(fn_name, stage, execution_modes, interface_ids)
                    .ok()
                    .unwrap();

                func.ret_ty = Type::Void;
                func
            } else {
                // Standard function
                let mut func = self.builder.define_function_named(fn_name);

                func.params = params;

                let return_ty = self.rust_ty_to_spirv_ref(self.mir.return_ty)?;
                if let SpirvType::Ref{ mutable: true, .. } = return_ty {
                    err = Some(self.tcx.sess.struct_err("Mutable references as return type are currently unsupported"));
                }
                self.return_ids = if Type::Void == *return_ty.ty() {
                    None
                } else {
                    let id = self.builder.alloc_id();
                    let local_var = LocalVar {
                        id: id,
                        ty: return_ty.clone().into(),
                    };
                    func.variables.push(local_var);
                    Some(FuncReturn::Return((id, return_ty.clone())))
                };

                func.ret_ty = return_ty.into();
                func
            };

            if let Some(mut err) = err {
                if let Some(source) = return_ptr.source_info { err.set_span(source.span); }
                return Err(err)
            }

            func  
        };

        println!("{:?}", (self.node_id, self.tcx.map.name(self.node_id).as_str(), self.mir));
        self.fn_ids.insert((did, signature.clone()), fn_module.id);
        self.trans(fn_module)
    }

    fn trans(&'e mut self, mut fn_module: inspirv_builder::Function) -> PResult<'e, ()> {
        // local variables and temporaries
        self.local_ids = {
            let mut ids: IndexVec<Local, Option<IdAndType>> = IndexVec::new();
            for (i, local) in self.mir.local_decls.iter().enumerate() {
                if i < self.mir.arg_count + 1 {
                    continue;
                }
                let id = self.builder.alloc_id();
                let ty = self.rust_ty_to_spirv_ref(local.ty)?;
                if Type::Void == *ty.ty() {
                    ids.push(None);
                } else {
                    let local_var = LocalVar {
                        id: id,
                        ty: ty.clone().into(),
                    };
                    fn_module.variables.push(local_var);
                    ids.push(Some((id, ty)));
                    if let Some(name) = local.name {
                        self.builder.name_id(id, &*name.as_str()); // TODO: hide this behind a function module interface
                    }
                }
            }
            ids
        };

        // Translate blocks
        let mut block_labels: IndexVec<BasicBlock, Id> = IndexVec::new();
        for _ in self.mir.basic_blocks().iter() {
            let block = fn_module.add_block(self.builder.alloc_id());
            block_labels.push(block.label);
        }

        for (i, bb) in self.mir.basic_blocks().iter().enumerate() {
            println!("bb{}: {:#?}", i, bb);

            let mut block_ctxt = InspirvBlock {
                ctxt: self,
                block: &mut fn_module.blocks[i],
                labels: &block_labels,
            };

            for stmt in &bb.statements {
                let result = block_ctxt.trans_stmnt(stmt);
                if let Err(mut err) = result {
                    err.emit();
                    return Err(self.tcx.sess.struct_err("Error on resolving basic block"));
                }
            }

            let result = block_ctxt.trans_terminator(&fn_module.ret_ty, bb.terminator());
            if let Err(mut err) = result {
                err.emit();
                return Err(self.tcx.sess.struct_err("Error on resolving terminator"));
            }
        }

        // Push function and clear variable stack
        self.builder.push_function(fn_module);
        self.arg_ids = IndexVec::new();
        self.local_ids = IndexVec::new();

        Ok(())
    }

    // TODO: remove ugly clones if possible
    fn resolve_lvalue(&mut self, lvalue: &Lvalue<'tcx>) -> PResult<'e, SpirvLvalue> {
        use rustc::mir::repr::Lvalue::*;
        use inspirv::core::enumeration::StorageClass::*;
        use self::SpirvType::*;
        match *lvalue {
            Local(id) => {
                let idx = id.index();
                if idx == 0 {
                    // return value
                    match self.return_ids {
                        Some(FuncReturn::Return((var_id, ref var_ty))) => Ok(SpirvLvalue::Return((var_id, var_ty.clone()))),
                        Some(FuncReturn::Interface(ref interfaces)) => Ok(SpirvLvalue::SignatureStruct(interfaces.clone(), StorageClassOutput)),
                        None => Ok(SpirvLvalue::Ignore),
                    }
                } else if idx < (self.arg_ids.len() + 1) {
                    // arguments
                    let id = Idx::new(idx - 1);
                    if let Some(arg) = self.arg_ids[id].clone() {
                        match arg {
                            FuncArg::Argument((id, ty)) => Ok(SpirvLvalue::Variable(id, ty, StorageClassFunction)),
                            FuncArg::Interface(interfaces) => Ok(SpirvLvalue::SignatureStruct(interfaces, StorageClassInput)),
                            FuncArg::ConstBuffer((id, ty)) => Ok(SpirvLvalue::Variable(id, ty, StorageClassUniform)),
                        }
                    } else {
                        Ok(SpirvLvalue::Ignore) // unnamed argument `_`
                    }
                } else {
                    // locals
                    let id = Idx::new(idx - (self.arg_ids.len() + 1));
                    if let Some((var_id, var_ty)) = self.local_ids[id].clone() {
                        Ok(SpirvLvalue::Variable(var_id, var_ty, StorageClassFunction))
                    } else {
                        Ok(SpirvLvalue::Ignore)
                    }
                }
            }
            Static(_def_id) => {
                let err = self.tcx.sess.struct_err("inspirv: Unsupported lvalue static!");
                Err(err)
            }
            Projection(ref proj) => {
                let base = self.resolve_lvalue(&proj.base)?;
                match (&proj.elem, &base) {
                    (&ProjectionElem::Field(field, _), &SpirvLvalue::SignatureStruct(ref interfaces, storage_class)) => {
                        let var = interfaces[field.index()].clone();
                        Ok(SpirvLvalue::Variable(var.0, SpirvType::NoRef(var.1), storage_class))
                    }
                    (&ProjectionElem::Field(field, ty), &SpirvLvalue::Variable(id, _, storage_class)) => {
                        let field_id = self.builder.define_constant(module::Constant::Scalar(ConstValue::U32(field.index() as u32)));
                        Ok(SpirvLvalue::AccessChain(id, storage_class, vec![field_id], self.rust_ty_to_spirv(ty)?))
                    }
                    (&ProjectionElem::Field(field, ty), &SpirvLvalue::AccessChain(id, storage_class, ref chain, _)) => {
                        let field_id = self.builder.define_constant(module::Constant::Scalar(ConstValue::U32(field.index() as u32)));
                        let mut chain = chain.clone();
                        chain.push(field_id);
                        Ok(SpirvLvalue::AccessChain(id, storage_class, chain, self.rust_ty_to_spirv(ty)?))
                    }
                    (&ProjectionElem::Deref, &SpirvLvalue::Variable(_id, Ref {ref ty, referent: Some(refer), ..}, storage_class)) => {
                        Ok(SpirvLvalue::Variable(refer, SpirvType::NoRef(ty.clone()), storage_class))
                    }
                    (&ProjectionElem::Deref, &SpirvLvalue::Variable(id, Ref {ref ty, referent: None, ..}, storage_class)) => {
                        Ok(SpirvLvalue::Variable(id, SpirvType::NoRef(ty.clone()), storage_class))
                    }
                    _ => {
                        let err = self.tcx.sess.struct_err("inspirv: Unsupported lvalue projection!");
                        Err(err)
                    }
                }
            }
        }
    }

    // Retrieve reference to the type of the lvalue
    // Needed for assignment of references to keep pass the referent
    fn resolve_ref_lvalue<'a>(&'a mut self, lvalue: &'a Lvalue<'tcx>) -> Option<&'a mut SpirvType> {
        use rustc::mir::repr::Lvalue::*;
        match *lvalue {
            Local(id) => {
                let idx = id.index();
                if idx == 0 {
                    match self.return_ids {
                        Some(FuncReturn::Return((_, ref mut var_ty))) => Some(var_ty),
                        _ => None,
                    }
                } else if idx < (self.arg_ids.len() + 1) {
                    let id = Idx::new(idx - 1);
                    if let Some(ref mut arg) = self.arg_ids[id] {
                        match *arg {
                            FuncArg::Argument((_, ref mut ty)) => Some(ty),
                            FuncArg::Interface(_) | FuncArg::ConstBuffer(_) => None,
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    let id = Idx::new(idx - self.arg_ids.len() - 1);
                    if let Some((_, ref mut var_ty)) = self.local_ids[id] {
                        Some(var_ty)
                    } else {
                        None
                    }
                }
            }
            Static(_def_id) => {
                println!("inspirv: unsupported lvalue {:?}", lvalue);
                None
            }
            // We don't support fields with reference types
            Projection(_) => None,
        }
    }

    // Lift lvalue to an simplier type if possible
    fn transform_lvalue(&mut self, block: &mut Block, lvalue: SpirvLvalue) -> SpirvLvalue {
        match lvalue {
            SpirvLvalue::AccessChain(root_id, storage_class, ref chain, ref ty) => {
                let chain_id = self.builder.alloc_id();
                let ty_id = self.builder.define_type(&Type::Pointer(Box::new(ty.clone()), storage_class));
                let op_access_chain = OpAccessChain(ty_id, chain_id, root_id, chain.clone());
                block.emit_instruction(op_access_chain);
                SpirvLvalue::Variable(chain_id, SpirvType::NoRef(ty.clone()), storage_class)
            },
            _ => lvalue
        }
    }

    fn get_node_id(&self, id: DefId) -> NodeId {
        // TODO: low-mid: unsafe! We would like to find the attributes of the current type, to look for representations as vector/matrix
        // Dont know how to correctly retrieve this information for non-local crates, probably requires custom crate format!
        self.tcx.map.as_local_node_id(id).expect("Id not defined in local crate!")
    }

    fn get_node_attributes(&self, id: DefId) -> PResult<'e, Vec<Attribute>> {
        let node_id = self.get_node_id(id);
        attribute::parse(self.tcx.sess, self.tcx.map.attrs(node_id))
    }

    fn rust_ty_to_spirv(&self, t: Ty<'tcx>) -> PResult<'e, Type> {
        use self::SpirvType::*;
        match self.rust_ty_to_spirv_ref(t)? {
            NoRef(ty) => Ok(ty),
            Ref{..} => bug!("Unallowed reference type ({:?})", t.sty),
        }
    }

    // TODO: low: We could cache some aggregated types for faster compilation
    fn rust_ty_to_spirv_ref(&self, t: Ty<'tcx>) -> PResult<'e, SpirvType> {
        use self::SpirvType::*;
        match t.sty {
            ty::TyBool => Ok(NoRef(Type::Bool)),
            ty::TyInt(IntTy::I8)      => Ok(NoRef(Type::Int(8, true))),
            ty::TyInt(IntTy::I16)     => Ok(NoRef(Type::Int(16, true))),
            ty::TyInt(IntTy::Is) |
            ty::TyInt(IntTy::I32)     => Ok(NoRef(Type::Int(32, true))), // isize
            ty::TyInt(IntTy::I64)     => Ok(NoRef(Type::Int(64, true))),
            ty::TyChar |
            ty::TyUint(UintTy::U8)    => Ok(NoRef(Type::Int(8, false))),
            ty::TyUint(UintTy::U16)   => Ok(NoRef(Type::Int(16, false))),
            ty::TyUint(UintTy::Us) |
            ty::TyUint(UintTy::U32)   => Ok(NoRef(Type::Int(32, false))), // usize
            ty::TyUint(UintTy::U64)   => Ok(NoRef(Type::Int(64, false))),
            ty::TyFloat(FloatTy::F32) => Ok(NoRef(Type::Float(32))),
            ty::TyFloat(FloatTy::F64) => Ok(NoRef(Type::Float(64))),
            ty::TyArray(_ty, _len)    => unimplemented!(),
            
            // TyNever:
            //  Some weird case, appearing sometimes in the code for whatever reason
            //  Often as unused temporary variables, which are never really used
            // TyTuple(&[]):
            //  Rust seems to emit () instead of void for function return types
            ty::TyNever => Ok(NoRef(Type::Void)),
            ty::TyTuple(tys) if tys.is_empty() => Ok(NoRef(Type::Void)),
            ty::TyTuple(tys) => Ok(NoRef(Type::Struct(tys.iter().map(|ty| self.rust_ty_to_spirv(ty)).collect::<PResult<Vec<_>>>()?))),

            //
            ty::TyAdt(adt, subs) if adt.is_struct() => {
                let attrs = self.get_node_attributes(adt.did)?;
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
                            let base = self.rust_ty_to_spirv(adt.struct_variant().fields[0].ty(*self.tcx, subs))?;
                            Ok(NoRef(Type::Vector {
                                base: Box::new(base),
                                components: components as u32,
                            }))
                        }
                        Attribute::Matrix { rows, cols } => {
                            let base = self.rust_ty_to_spirv(adt.struct_variant().fields[0].ty(*self.tcx, subs))?;
                            if let Type::Vector { base, .. } = base {
                                Ok(NoRef(Type::Matrix {
                                    base: base,
                                    rows: rows as u32,
                                    cols: cols as u32,
                                }))
                            } else {
                                bug!("Unexpected matrix base type ({:?})", base)
                            }                            
                        }
                        _ => bug!("Unhandled internal type ({:?})", *internal_type),
                    }
                } else if wrapper_type {
                    self.rust_ty_to_spirv_ref(adt.struct_variant().fields[0].ty(*self.tcx, subs))
                } else {
                    // an actual struct!
                    // TODO: handle names
                    Ok(NoRef(Type::Struct(
                        adt.struct_variant()
                           .fields
                           .iter()
                           .map(|field|
                                self.rust_ty_to_spirv(
                                    field.ty(*self.tcx, subs)
                                ))
                           .collect::<PResult<Vec<_>>>()?
                        )))
                }    
            }
            ty::TyAdt(adt, _subs) if adt.is_enum() => {
                use rustc_const_math::ConstInt::*;
                use rustc_const_math::ConstIsize::*;

                if adt.variants.is_empty() {
                    // TODO: probably won't happen?
                    return Ok(NoRef(Type::Void))
                }

                let unit_only = adt.variants.iter().all(|variant| variant.ctor_kind == CtorKind::Const);
                if !unit_only {
                    bug!("inspirv: Enums can only contain unit type structs ({:?})", t.sty);
                }

                let disr = adt.variants[0].disr_val;
                let (bit_width, signed) = match disr {
                    I16(_) => (16, true),
                    I32(_) |
                    Isize(Is32(_)) => (32, true),
                    I64(_) => (64, true),
                    U16(_) => (16, false),
                    U32(_) => (32, false),
                    U64(_) => (64, false),
                    _ => bug!("inspirv: Unsupported enum base type ({:?})", disr),
                };

                Ok(NoRef(Type::Int(bit_width, signed)))
            }

            ty::TyRef(_, ty_mut) => {
                Ok(Ref {
                    ty: self.rust_ty_to_spirv(ty_mut.ty)?,
                    mutable: ty_mut.mutbl == hir::Mutability::MutMutable,
                    referent: None,
                })
            }

            ty::TyParam(param) => {
                let ty = param.to_ty(*self.tcx);
                let ty = monomorphize::apply_ty_substs(self.tcx, self.substs.unwrap(), ty);
                self.rust_ty_to_spirv_ref(ty)
            }

            _ => { println!("{:?}", t.sty); unimplemented!() },
        }
    }
}

pub struct InspirvBlock<'a: 'b, 'b, 'v: 'a, 'tcx: 'v> {
    pub ctxt: &'a mut InspirvFnCtxt<'v, 'tcx>,
    pub block: &'b mut Block,
    pub labels: &'b IndexVec<BasicBlock, Id>,
}

impl<'a: 'b, 'b: 'e, 'v: 'a, 'tcx: 'v, 'e> InspirvBlock<'a, 'b, 'v, 'tcx> {
    fn trans_stmnt(&mut self, stmt: &Statement<'tcx>) -> PResult<'e, ()>{
        match stmt.kind {
            StatementKind::Assign(ref assign_lvalue, ref rvalue) => {
                println!("{:?}", (assign_lvalue, rvalue));
                let lvalue = self.ctxt.resolve_lvalue(assign_lvalue)?;
                let lvalue = self.ctxt.transform_lvalue(self.block, lvalue);
            
                match lvalue {
                    SpirvLvalue::Variable(lvalue_id, lvalue_ty, _) | SpirvLvalue::Return((lvalue_id, lvalue_ty)) => {
                        use rustc::mir::repr::Rvalue::*;
                        match *rvalue {
                            Use(ref operand) => {
                                let op = self.trans_operand(operand)?;
                                match op {
                                    SpirvOperand::Constant(op_id, _) => {
                                        self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                    }
                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, SpirvType::NoRef(op_ty), _)) => {
                                        let op_id = self.ctxt.builder.alloc_id();
                                        self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                        self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                    }
                                    SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, SpirvType::Ref{ referent, .. }, _)) => {
                                        // Just pass the referent to the lvalue reference
                                        let ref_id = if let Some(referent) = referent { referent } else { op_ptr_id };
                                        if let Some(&mut SpirvType::Ref{ref mut referent, ..}) = self.ctxt.resolve_ref_lvalue(assign_lvalue) {
                                            *referent = Some(ref_id);
                                        } else {
                                            self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                               "inspirv: Unsupported rvalue reference!")
                                        }
                                    }
                                    SpirvOperand::Consume(SpirvLvalue::SignatureStruct(ref interfaces, _)) => {
                                        let ids = interfaces.iter().map(|interface| {
                                            let id = self.ctxt.builder.alloc_id();
                                            self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&interface.1), id, interface.0, None));
                                            id
                                        }).collect::<Vec<_>>();
                                        let composite_id = self.ctxt.builder.alloc_id();
                                        self.block.emit_instruction(OpCompositeConstruct(self.ctxt.builder.define_type(&lvalue_ty.into()), composite_id, ids));
                                        self.block.emit_instruction(OpStore(lvalue_id, composite_id, None));
                                    }
                                    _ => {
                                        println!("{:?}", op);
                                        self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                       "inspirv: Unsupported rvalue!");
                                    }
                                }
                            }

                            /// [x; 32]
                            Repeat(ref _operand, ref _times) => {}

                            Ref(_, _, ref referent) => {
                                let referent = self.ctxt.resolve_lvalue(referent).expect("inspirv: Unable to resolve referent lvalue");
                                let referent = self.ctxt.transform_lvalue(self.block, referent);
                                if let SpirvLvalue::Variable(referent_id, _, _) = referent {
                                    if let Some(&mut SpirvType::Ref{ref mut referent, ..}) = self.ctxt.resolve_ref_lvalue(assign_lvalue) {
                                        *referent = Some(referent_id);
                                    } else {
                                        self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                           "inspirv: Unsupported rvalue reference!")
                                    }
                                } else {
                                    self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                       "inspirv: Unsupported rvalue reference!")
                                }
                            }

                            /// length of a [X] or [X;n] value
                            Len(_ /* ref val */) => {}

                            Cast(ref kind, ref operand, ty) => {
                                if *kind != CastKind::Misc {
                                    self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported cast kind!")
                                } else {
                                    let op = self.trans_operand(operand)?;
                                    let cast_ty = self.ctxt.rust_ty_to_spirv(ty)?;
                                    match op {
                                        SpirvOperand::Constant(_op_id, _op_ty) => {
                                            // Why!? ):
                                            // Casting an constant is probably not the thing you want to do in the first place
                                            // TODO: low
                                            self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported const cast rvalue (soon)!")
                                            // self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                        }
                                        SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                            let op_id = self.ctxt.builder.alloc_id();
                                            self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                            // TODO: add cast conversions
                                            match (cast_ty, op_ty) {
                                                _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unsupported cast conversion!"),
                                            }

                                            self.block.emit_instruction(OpStore(lvalue_id, op_id, None));
                                        }
                                        _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                           "inspirv: Unsupported cast rvalue!"),
                                    }
                                }
                            }

                            BinaryOp(ref op, ref left, ref right) |
                            CheckedBinaryOp(ref op, ref left, ref right) => {
                                let left = self.trans_operand(left)?;
                                let right = self.trans_operand(right)?;
                                println!("binop: {:?}", op);

                                match (left, right) {
                                    (SpirvOperand::Consume(SpirvLvalue::Variable(left_id, left_ty, _)),
                                     SpirvOperand::Consume(SpirvLvalue::Variable(right_id, right_ty, _))) => {
                                        let left_ptr_id = self.ctxt.builder.alloc_id();
                                        let right_ptr_id = self.ctxt.builder.alloc_id();

                                        // load variable values
                                        let op_load_left = OpLoad(self.ctxt.builder.define_type(&left_ty), left_ptr_id, left_id, None);
                                        let op_load_right = OpLoad(self.ctxt.builder.define_type(&right_ty), right_ptr_id, right_id, None);
                                        self.block.emit_instruction(op_load_left);
                                        self.block.emit_instruction(op_load_right);

                                        self.emit_binop(*op, (lvalue_id, lvalue_ty), (left_ptr_id, left_ty), (right_ptr_id, right_ty))?;
                                    }

                                    (SpirvOperand::Consume(SpirvLvalue::Variable(left_id, left_ty, _)),
                                     SpirvOperand::Constant(right_id, right_ty)) => {
                                        let left_ptr_id = self.ctxt.builder.alloc_id();

                                        // load variable value
                                        let op_load_left = OpLoad(self.ctxt.builder.define_type(&left_ty), left_ptr_id, left_id, None);
                                        self.block.emit_instruction(op_load_left);

                                        self.emit_binop(*op, (lvalue_id, lvalue_ty), (left_ptr_id, left_ty), (right_id, right_ty))?;
                                    }

                                    (SpirvOperand::Constant(left_id, left_ty),
                                     SpirvOperand::Consume(SpirvLvalue::Variable(right_id, right_ty, _))) => {
                                        let right_ptr_id = self.ctxt.builder.alloc_id();

                                        // load variable value
                                        let op_load_right = OpLoad(self.ctxt.builder.define_type(&right_ty), right_ptr_id, right_id, None);
                                        self.block.emit_instruction(op_load_right);

                                        self.emit_binop(*op, (lvalue_id, lvalue_ty), (left_id, left_ty), (right_ptr_id, right_ty))?;
                                    }

                                    (SpirvOperand::Constant(left_id, left_ty),
                                     SpirvOperand::Constant(right_id, right_ty)) => {
                                        self.emit_binop(*op, (lvalue_id, lvalue_ty), (left_id, left_ty), (right_id, right_ty))?;
                                    }

                                    // TODO:
                                    _ => (),
                                }
                            }

                            UnaryOp(ref op, ref operand) => {
                                let _operand = self.trans_operand(operand)?;
                                println!("unop: {:?}", op);
                                // TODO
                            }

                            Aggregate(ref kind, ref _operands) => {
                                match *kind {
                                    // Only care about c-enums, we can't handle the other things
                                    AggregateKind::Adt(adt, index, _, _) if adt.is_enum() => {
                                        use rustc_const_math::ConstInt::*;
                                        use rustc_const_math::ConstIsize::*;

                                        let disr = adt.variants[index].disr_val;
                                        println!("{:?}", disr);

                                        let constant = match disr {
                                            I16(v) => module::Constant::Scalar(ConstValue::I16(v)),
                                            I32(v) |
                                            Isize(Is32(v)) => module::Constant::Scalar(ConstValue::I32(v)),
                                            I64(v) => module::Constant::Scalar(ConstValue::I64(v)),
                                            U16(v) => module::Constant::Scalar(ConstValue::U16(v)),
                                            U32(v) => module::Constant::Scalar(ConstValue::U32(v)),
                                            U64(v) => module::Constant::Scalar(ConstValue::U64(v)),
                                            _ => bug!("inspirv: Unsupported enum base type ({:?})", disr),
                                        };

                                        let constant_id = self.ctxt.builder.define_constant(constant);
                                        self.block.emit_instruction(OpStore(lvalue_id, constant_id, None));
                                    }
                                    // TODO: structs
                                    _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Unhandled aggregate type"),
                                }                                   
                            }

                            Box(..) => {
                                self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid box r-value")
                            }
                            InlineAsm { .. } => {
                                self.ctxt.tcx.sess.span_err(stmt.source_info.span, "inspirv: Invalid inline asm")
                            }
                        }
                    }

                    SpirvLvalue::SignatureStruct(ref interfaces, _) => {
                        use rustc::mir::repr::Rvalue::*;
                        match *rvalue {
                            Use(ref _operand) => {
                                // TODO:
                                self.ctxt.tcx.sess.span_warn(stmt.source_info.span,
                                            "inspirv: Unhandled use-assignment for interfaces (soon)!")
                            }

                            Aggregate(ref _kind, ref operands) => {
                                for (operand, interface) in operands.iter().zip(interfaces.iter()) {
                                    let op = self.trans_operand(operand)?;
                                    match op {
                                        SpirvOperand::Constant(op_id, _) => {
                                            self.block.emit_instruction(OpStore(interface.0, op_id, None));
                                        }
                                        SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, op_ty, _)) => {
                                            let op_id = self.ctxt.builder.alloc_id();
                                            self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&op_ty), op_id, op_ptr_id, None));
                                            self.block.emit_instruction(OpStore(interface.0, op_id, None));
                                        }
                                        _ => self.ctxt.tcx.sess.span_err(stmt.source_info.span,
                                                           "inspirv: Unsupported aggregate operand!"),
                                    }
                                }
                            }

                            _ => bug!("Unexpected rvalue for an interface ({:?})", rvalue), // TODO: really a bug?
                        }
                    }

                    SpirvLvalue::Ignore => (),
                    SpirvLvalue::AccessChain(..) => unreachable!(),        
                }
            }
            // Translation only
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
            // Empty statements, nothing to do
            | StatementKind::Nop => {}

            StatementKind::SetDiscriminant { .. } => println!("{:?}", stmt.kind),
        }

        Ok(())
    }

    fn trans_terminator(&'e mut self, ret_ty: &Type, terminator: &Terminator<'tcx>) -> PResult<'e, ()> {
        use rustc::mir::repr::TerminatorKind::*;
        match terminator.kind {
            Return => {
                match (ret_ty, &self.ctxt.return_ids) {
                    (&Type::Void, _) | (_, &None) => {
                        self.block.branch_instr = Some(BranchInstruction::Return(OpReturn));
                    }
                    (_, &Some(FuncReturn::Return((id, ref ty)))) => {
                        use self::SpirvType::*;
                        let load_id = match *ty {
                            NoRef(ref ty) => {
                                let load_id = self.ctxt.builder.alloc_id();
                                let op_load = OpLoad(self.ctxt.builder.define_type(ty), load_id, id, None);
                                self.block.emit_instruction(op_load);
                                load_id
                            }
                            Ref { referent, .. } => referent.unwrap(),
                        };
                        self.block.branch_instr = Some(BranchInstruction::ReturnValue(OpReturnValue(load_id)));
                    }
                    (_, &Some(FuncReturn::Interface(..))) => unreachable!(),
                }
            }

            Unreachable => {
                self.block.branch_instr = Some(BranchInstruction::Unreachable(OpUnreachable));
            }

            If { ref cond, targets: (branch_true, branch_false) } => {
                let cond = self.trans_operand(cond)?;
                let cond_id = match cond {
                    SpirvOperand::Consume(SpirvLvalue::Variable(id, ty, _)) => {
                        let load_id = self.ctxt.builder.alloc_id();
                        self.block.emit_instruction(OpLoad(self.ctxt.builder.define_type(&ty), load_id, id, None));
                        load_id
                    },

                    SpirvOperand::Constant(id, _) => id,

                    _ => return Err(self.ctxt.tcx.sess.struct_span_err(terminator.source_info.span, "inspirv: Unhandled if condition operand.")),
                };

                self.block.branch_instr = Some(
                    BranchInstruction::BranchConditional(
                        OpBranchConditional(
                            cond_id,
                            self.labels[branch_true],
                            self.labels[branch_false],
                            Vec::new(),
                        )));
            }

            // &Switch { discr, adt_def, targets } => { },
            // &SwitchInt { discr, switch_ty, values, targets } => { },
            Resume => self.block.branch_instr = Some(BranchInstruction::Return(OpReturn)),
            Drop { target, .. } => self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[target]))),
            // &DropAndReplace { location, value, target, unwind } => { },

            Call { ref func, ref args, ref destination, .. } => {
                let func_op = self.trans_operand(func)?;
                match func_op {
                    SpirvOperand::FnCall(mut def_id, substs) => {
                        let fn_ty = self.ctxt.tcx.lookup_item_type(def_id).ty;
                        let signature = fn_ty.fn_sig().skip_binder();

                        let (substs, signature) = if self.ctxt.tcx.trait_of_item(def_id).is_some() {
                            let (resolved_def_id, resolved_substs) = traits::resolve_trait_method(self.ctxt.tcx, def_id, substs);
                            let ty = self.ctxt.tcx.lookup_item_type(resolved_def_id).ty;
                            // TODO: investigate rustc trans use of liberate_bound_regions or similar here
                            let signature = ty.fn_sig().skip_binder();

                            def_id = resolved_def_id;
                            (resolved_substs, signature)
                        } else {
                            (substs, signature)
                        };

                        let attrs = self.ctxt.get_node_attributes(def_id)?;

                        let intrinsic = attrs.iter().find(|attr| match **attr {
                            Attribute::Intrinsic (..) => true,
                            _ => false,
                        });

                        let (lvalue, next_block) = destination.clone().expect("Call without destination, interesting!");
                        let lvalue = self.ctxt.resolve_lvalue(&lvalue).map(|lvalue| self.ctxt.transform_lvalue(self.block, lvalue)).expect("Unhandled lvalue");

                        // Translate function call
                        let id = if let Some(&Attribute::Intrinsic(ref intrinsic)) = intrinsic {
                            self.emit_intrinsic(intrinsic, args)?
                        } else {
                            // 'normal' function call
                            let args_ops = args.iter().map(|arg| self.trans_operand(arg)).collect::<PResult<Vec<_>>>()?;
                            let component_ids = args_ops.iter().filter_map(
                                                    |arg| match *arg {
                                                        SpirvOperand::Constant(c, _) => Some(c),
                                                        SpirvOperand::Consume(SpirvLvalue::Variable(_, SpirvType::Ref { referent, .. } , _)) => referent,
                                                        SpirvOperand::Consume(SpirvLvalue::Variable(op_ptr_id, _, _)) => Some(op_ptr_id),
                                                        _ => None
                                                    }).collect::<Vec<_>>();

                            let signature = monomorphize::apply_param_substs(self.ctxt.tcx, substs, signature);

                            if !self.ctxt.fn_ids.contains_key(&(def_id, signature.clone())) {
                                let mut fn_ctxt = InspirvFnCtxt {
                                    tcx: self.ctxt.tcx,
                                    mir_map: self.ctxt.mir_map,
                                    mir: &self.ctxt.mir_map.map[&def_id],
                                    def_id: def_id,
                                    node_id: self.ctxt.get_node_id(def_id),
                                    builder: self.ctxt.builder,
                                    fn_ids: self.ctxt.fn_ids,
                                    substs: Some(substs),

                                    arg_ids: IndexVec::new(),
                                    local_ids: IndexVec::new(),
                                    return_ids: None,
                                };

                                let result = fn_ctxt.trans_fn(FnTrans::Required);
                                if let Err(mut err) = result {
                                    err.emit();
                                    return Err(self.ctxt.tcx.sess.struct_err("Stop due to error on translating function"));
                                }
                            }

                            let fn_id = self.ctxt.fn_ids[&(def_id, signature)];
                            let result_id = self.ctxt.builder.alloc_id();
                            let result_type = {
                                let ret_ty = self.ctxt.builder.get_function(fn_id).unwrap().ret_ty.clone();
                                self.ctxt.builder.define_type(&ret_ty)
                            };

                            self.block.emit_instruction(
                                OpFunctionCall(
                                    result_type,
                                    result_id,
                                    fn_id.0,
                                    component_ids
                                )
                            );
                            result_id
                        };

                        // Store return value into lvalue destination
                        match lvalue {
                            SpirvLvalue::Variable(lvalue_id, _, _) | SpirvLvalue::Return((lvalue_id, _)) => {
                                self.block.emit_instruction(OpStore(lvalue_id, id, None));
                            },

                            SpirvLvalue::Ignore => (),

                            _ => self.ctxt.tcx.sess.span_err(terminator.source_info.span, "inspirv: Unhandled lvalue for call terminator!"),
                        }

                        self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[next_block])));
                    }

                    _ => bug!("Unexpected operand type, expected `FnCall` ({:?})", func_op),
                }
            },
            //

            Goto { ref target } | Assert { ref target, .. } => {
                // Ignore the actual asset
                // TODO: correct behaviour? some conditions?
                self.block.branch_instr = Some(BranchInstruction::Branch(OpBranch(self.labels[*target])));
            },
            
            _ => { println!("Unhandled terminator kind: {:?}", terminator.kind); }, //unimplemented!(),
        }
        Ok(())
    }

    pub fn trans_operand(&mut self, operand: &Operand<'tcx>) -> PResult<'e, SpirvOperand<'tcx>> {
        use rustc::mir::repr::Operand::*;
        match *operand {
            Consume(ref lvalue) => {
                let lvalue = self.ctxt.resolve_lvalue(lvalue)?;
                let lvalue = self.ctxt.transform_lvalue(self.block, lvalue);
                Ok(SpirvOperand::Consume(lvalue))
            }

            Constant(ref c) => {
                match c.literal {
                    Literal::Item { def_id, substs } => {
                        Ok(SpirvOperand::FnCall(def_id, substs))
                    }
                    Literal::Value { ref value } => {
                        let (constant, ty) = match *value {
                            Float(ConstFloat::F32(v)) => (module::Constant::Float(ConstValueFloat::F32(v)), Type::Float(32)),
                            Float(ConstFloat::F64(v)) => (module::Constant::Float(ConstValueFloat::F64(v)), Type::Float(64)),
                            Float(ConstFloat::FInfer { .. }) => bug!("MIR must not use `{:?}`", c.literal),
                            Integral(ConstInt::I8(..)) => bug!("Inspirv: `i8` are not supported for shaders `{:?}`", c.literal),
                            Integral(ConstInt::I16(v)) => (module::Constant::Scalar(ConstValue::I16(v)), Type::Int(16, true)),
                            Integral(ConstInt::I32(v)) => (module::Constant::Scalar(ConstValue::I32(v)), Type::Int(32, true)),
                            Integral(ConstInt::I64(v)) => (module::Constant::Scalar(ConstValue::I64(v)), Type::Int(64, true)),
                            Integral(ConstInt::Isize(_v)) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Integral(ConstInt::U8(..)) => bug!("Inspirv: `u8` are not supported for shaders `{:?}`", c.literal),
                            Integral(ConstInt::U16(v)) => (module::Constant::Scalar(ConstValue::U16(v)), Type::Int(16, false)),
                            Integral(ConstInt::U32(v)) => (module::Constant::Scalar(ConstValue::U32(v)), Type::Int(32, false)),
                            Integral(ConstInt::U64(v)) => (module::Constant::Scalar(ConstValue::U64(v)), Type::Int(64, false)),
                            Integral(ConstInt::Usize(_v)) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Bool(val) => (module::Constant::Scalar(ConstValue::Bool(val)), Type::Bool),
                            Char(_val) => bug!("Currently unsupported constant literal `{:?}`", c.literal),
                            Integral(ConstInt::Infer(_))
                            | Integral(ConstInt::InferSigned(_)) => bug!("MIR must not use `{:?}`", c.literal),
                            Str(_) => bug!("Currently unsupported constant literal `{:?}`", c.literal), // TODO: unsupported
                            ByteStr(ref _v) => bug!("Currently unsupported constant literal `{:?}`", c.literal), // TODO: unsupported?
                            Struct(_)
                            | Tuple(_)
                            | Array(..)
                            | Repeat(..)
                            | Function(_) => bug!("MIR must not use `{:?}` (which refers to a local ID)", c.literal),
                            Dummy => bug!(),
                        };

                        let constant_id = self.ctxt.builder.define_constant(constant);
                        Ok(SpirvOperand::Constant(constant_id, SpirvType::NoRef(ty)))
                    }
                    Literal::Promoted { .. /* ref index */ } => unimplemented!(),
                }
            }
        }
    }

    fn emit_binop(&mut self, op: BinOp, (result_id, result_ty): IdAndType, (left_id, left_ty): IdAndType, (right_id, right_ty): IdAndType) -> PResult<'e, ()> {
        use self::SpirvType::*;

        // emit instructions
        let add_result = self.ctxt.builder.alloc_id();
        let op_binop: instruction::Instruction = match (op, &left_ty, &right_ty) {
            // arithmetic operators
            (BinOp::Add, &NoRef(Type::Int(..)), &NoRef(Type::Int(..))) => {
                OpIAdd(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Add, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFAdd(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Sub, &NoRef(Type::Int(..)), &NoRef(Type::Int(..))) => {
                OpISub(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Sub, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFSub(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Mul, &NoRef(Type::Int(..)), &NoRef(Type::Int(..))) => {
                OpIMul(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Mul, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFMul(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Div, &NoRef(Type::Int(_, true)), &NoRef(Type::Int(_, true))) => {
                OpSDiv(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Div, &NoRef(Type::Int(_, false)), &NoRef(Type::Int(_, false))) => {
                OpUDiv(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Div, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFDiv(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            // logical operators
            (BinOp::Eq, &NoRef(Type::Int(..)), &NoRef(Type::Int(..))) => {
                OpIEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Ne, &NoRef(Type::Int(..)), &NoRef(Type::Int(..))) => {
                OpINotEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Lt, &NoRef(Type::Int(_, false)), &NoRef(Type::Int(_, false))) => {
                OpULessThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Le, &NoRef(Type::Int(_, false)), &NoRef(Type::Int(_, false))) => {
                OpULessThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Gt, &NoRef(Type::Int(_, false)), &NoRef(Type::Int(_, false))) => {
                OpUGreaterThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Ge, &NoRef(Type::Int(_, false)), &NoRef(Type::Int(_, false))) => {
                OpUGreaterThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Lt, &NoRef(Type::Int(_, true)), &NoRef(Type::Int(_, true))) => {
                OpSLessThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Le, &NoRef(Type::Int(_, true)), &NoRef(Type::Int(_, true))) => {
                OpSLessThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Gt, &NoRef(Type::Int(_, true)), &NoRef(Type::Int(_, true))) => {
                OpSGreaterThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Ge, &NoRef(Type::Int(_, true)), &NoRef(Type::Int(_, true))) => {
                OpSGreaterThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            // TODO: ordered or unordered?
            (BinOp::Eq, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Ne, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdNotEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            (BinOp::Lt, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdLessThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Le, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdLessThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Gt, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdGreaterThan(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }
            (BinOp::Ge, &NoRef(Type::Float(..)), &NoRef(Type::Float(..))) => {
                OpFOrdGreaterThanEqual(self.ctxt.builder.define_type(&result_ty), add_result, left_id, right_id).into()
            }

            _ => bug!("Unexpected binop combination ({:?})", (op, left_ty, right_ty)),
        };

        self.block.emit_instruction(op_binop);
        
        // store
        self.block.emit_instruction(OpStore(result_id, add_result, None));
        Ok(())
    }
}
