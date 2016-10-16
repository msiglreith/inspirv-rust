#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
extern crate inspirv;
extern crate inspirv_rust;
extern crate rustc;
extern crate rustc_driver;

use inspirv_rust::trans;
use rustc::session::Session;
use rustc_driver::{driver, CompilerCalls};
use rustc::mir::mir_map::MirMap;
use std::process;
use std::fs::File;
use std::path::Path;

struct SpirvCompilerCalls;

impl<'a> CompilerCalls<'a> for SpirvCompilerCalls {
    fn build_controller(&mut self,
                        _: &Session,
                        _: &getopts::Matches)
                        -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.stop = rustc_driver::Compilation::Stop;
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

            if let Some(mut module) = trans::translate_to_spirv(&tcx, &mut mir_map_copy, state.analysis.unwrap()) {
                let ofile = state.out_file.unwrap_or(Path::new("example.spv"));
                println!("{:?}", ofile);
                let file = File::create(ofile).unwrap();

                module.export_binary(file);

                let file = File::open(ofile).unwrap();
                let mut reader = inspirv::read_binary::ReaderBinary::new(file).unwrap();

                while let Some(instr) = reader.read_instruction().unwrap() {
                    println!("{:?}", instr);
                }
            } else {
                println!("u wot");
            }
            
        });

        control
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
