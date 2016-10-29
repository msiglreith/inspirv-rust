#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
extern crate inspirv;
extern crate inspirv_rust;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_back;
extern crate rustc_trans;
extern crate rustc_lint;
extern crate rustc_metadata;
extern crate rustc_errors as errors;
extern crate syntax;

use inspirv_rust::trans;
use rustc_trans::back::link;
use rustc::dep_graph::DepGraph;
use rustc::session::{Session, build_session, early_error};
use rustc::session::config::{self, ErrorOutputType, Input, PrintRequest};
use rustc_driver::{driver, target_features, CompilerCalls, Compilation, RustcDefaultCalls};
use rustc::mir::mir_map::MirMap;
use rustc_metadata::cstore::CStore;
use rustc::lint;

use std::process;
use std::path::PathBuf;

use std::default::Default;
use std::rc::Rc;
use std::str;

use syntax::ast;
use syntax::feature_gate::{GatedCfg, UnstableFeatures};
use syntax::parse::{self, PResult};

struct SpirvCompilerCalls;

// copied from RustcDefaultCalls::print_crate_info
// TODO: remove if this ever goes public
fn print_crate_info(sess: &Session,
                    cfg: &ast::CrateConfig,
                    input: Option<&Input>,
                    odir: &Option<PathBuf>,
                    ofile: &Option<PathBuf>)
                    -> Compilation {
    if sess.opts.prints.is_empty() {
        return Compilation::Continue;
    }

    let attrs = match input {
        None => None,
        Some(input) => {
            let result = parse_crate_attrs(sess, input);
            match result {
                Ok(attrs) => Some(attrs),
                Err(mut parse_error) => {
                    parse_error.emit();
                    return Compilation::Stop;
                }
            }
        }
    };
    for req in &sess.opts.prints {
        match *req {
            PrintRequest::TargetList => {
                let mut targets = rustc_back::target::get_targets().collect::<Vec<String>>();
                targets.sort();
                println!("{}", targets.join("\n"));
            },
            PrintRequest::Sysroot => println!("{}", sess.sysroot().display()),
            PrintRequest::FileNames |
            PrintRequest::CrateName => {
                let input = match input {
                    Some(input) => input,
                    None => early_error(ErrorOutputType::default(), "no input file provided"),
                };
                let attrs = attrs.as_ref().unwrap();
                let t_outputs = driver::build_output_filenames(input, odir, ofile, attrs, sess);
                let id = link::find_crate_name(Some(sess), attrs, input);
                if *req == PrintRequest::CrateName {
                    println!("{}", id);
                    continue;
                }
                let crate_types = driver::collect_crate_types(sess, attrs);
                for &style in &crate_types {
                    let fname = link::filename_for_input(sess, style, &id, &t_outputs);
                    println!("{}",
                             fname.file_name()
                                  .unwrap()
                                  .to_string_lossy());
                }
            }
            PrintRequest::Cfg => {
                let allow_unstable_cfg = UnstableFeatures::from_environment()
                    .is_nightly_build();

                for cfg in cfg {
                    if !allow_unstable_cfg && GatedCfg::gate(&*cfg).is_some() {
                        continue;
                    }

                    if cfg.is_word() {
                        println!("{}", cfg.name());
                    } else if let Some(s) = cfg.value_str() {
                        println!("{}=\"{}\"", cfg.name(), s);
                    } else if cfg.is_meta_item_list() {
                        // Right now there are not and should not be any
                        // MetaItemKind::List items in the configuration returned by
                        // `build_configuration`.
                        panic!("Found an unexpected list in cfg attribute '{}'!", cfg.name())
                    } else {
                        // There also shouldn't be literals.
                        panic!("Found an unexpected literal in cfg attribute '{}'!", cfg.name())
                    }
                }
            }
            PrintRequest::TargetCPUs => {

            }
            PrintRequest::TargetFeatures => {

            }
            PrintRequest::RelocationModels => {

            }
            PrintRequest::CodeModels => {

            }
        }
    }
    return Compilation::Stop;
}

fn parse_crate_attrs<'a>(sess: &'a Session, input: &Input) -> PResult<'a, Vec<ast::Attribute>> {
    match *input {
        Input::File(ref ifile) => {
            parse::parse_crate_attrs_from_file(ifile, Vec::new(), &sess.parse_sess)
        }
        Input::Str { ref name, ref input } => {
            parse::parse_crate_attrs_from_source_str(name.clone(),
                                                     input.clone(),
                                                     Vec::new(),
                                                     &sess.parse_sess)
        }
    }
}

impl<'a> CompilerCalls<'a> for SpirvCompilerCalls {
    fn build_controller(&mut self,
                        _: &Session,
                        _: &getopts::Matches)
                        -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.stop = Compilation::Stop;
        control.after_analysis.callback = Box::new(move |state| {
            state.session.abort_if_errors();

            let tcx = state.tcx.unwrap();
            let mir_map = state.mir_map.unwrap();
            {
                println!("Pre-trans");
                tcx.print_debug_stats();
            }

            let mut mir_map_copy = MirMap::new(tcx.dep_graph.clone());
            for def_id in mir_map.map.keys() {
                mir_map_copy.map.insert(def_id, mir_map.map.get(&def_id).unwrap().clone());
            }

            {
                println!("Post-trans");
                tcx.print_debug_stats();
            }

            trans::translate_to_spirv(&tcx, &mut mir_map_copy, state.analysis.unwrap(), &state.out_dir);
        });

        control
    }

    fn no_input(&mut self,
                matches: &getopts::Matches,
                sopts: &config::Options,
                cfg: &ast::CrateConfig,
                odir: &Option<PathBuf>,
                ofile: &Option<PathBuf>,
                descriptions: &errors::registry::Registry)
                -> Option<(Input, Option<PathBuf>)> {
        match matches.free.len() {
            0 => {
                if sopts.describe_lints {
                    let mut ls = lint::LintStore::new();
                    rustc_lint::register_builtins(&mut ls, None);
                    // TODO: describe_lints(&ls, false);
                    return None;
                }
                let dep_graph = DepGraph::new(sopts.build_dep_graph());
                let cstore = Rc::new(CStore::new(&dep_graph));
                let sess = build_session(sopts.clone(),
                    &dep_graph,
                    None,
                    descriptions.clone(),
                    cstore.clone());
                rustc_lint::register_builtins(&mut sess.lint_store.borrow_mut(), Some(&sess));
                let mut cfg = config::build_configuration(&sess, cfg.clone());
                target_features::add_configuration(&mut cfg, &sess);
                let should_stop = print_crate_info(&sess,
                                                                      &cfg,
                                                                      None,
                                                                      odir,
                                                                      ofile);
                if should_stop == Compilation::Stop {
                    return None;
                }
                early_error(sopts.error_format, "no input filename given");
            }
            1 => panic!("make_input should have provided valid inputs"),
            _ => early_error(sopts.error_format, "multiple input filenames provided"),
        }

        None
    }

    fn late_callback(&mut self,
                     matches: &getopts::Matches,
                     sess: &Session,
                     cfg: &ast::CrateConfig,
                     input: &Input,
                     odir: &Option<PathBuf>,
                     ofile: &Option<PathBuf>)
                     -> Compilation {
        print_crate_info(sess, cfg, Some(input), odir, ofile)
            .and_then(|| RustcDefaultCalls::list_metadata(sess, matches, input))
    }
}

fn main() {
    env_logger::init().unwrap();

    let inspirv_compiler_args = ["-h", "--help"];
    let mut rustc_args: Vec<String> =
        std::env::args().filter(|arg| !inspirv_compiler_args.contains(&arg.as_ref())).collect();

    // TODO: use a command line parsing library
    for flag in std::env::args().filter(|arg| inspirv_compiler_args.contains(&arg.as_ref())) {
        match flag.as_ref() {
            "-h" | "--help" => {
                let usage = "inspirv-mir [OPTIONS] INPUT \n\nOptions: \n    -h, --help    Display \
                             this message";
                println!("usage: {}", usage);
                process::exit(0);
            }
            _ => panic!("unexpected compiler flag: {}", flag),
        }
    }

    // rustc_args.push("--target=etc/spirv.json".into());
    match rustc_driver::run_compiler(&rustc_args, &mut SpirvCompilerCalls, None, None) {
        (Ok(_), _) => process::exit(0),
        (Err(code), _) => { println!("error: {:?}", code); process::exit(code as i32) },
    }
}
