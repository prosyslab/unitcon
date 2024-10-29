open Utils
module C = Cmdliner
module Cmd = C.Cmd
module Arg = C.Arg
module Manpage = C.Manpage
module Term = C.Term

let build () =
  L.info "Start building";
  if !Cmdline.command_maker then CommandMaker.run !Cmdline.target_program
  else if !Cmdline.class_info then ClassInfo.run !Cmdline.out_dir
  else if !Cmdline.constant_info then ConstantInfo.run !Cmdline.out_dir
  else (
    CommandMaker.run !Cmdline.target_program;
    ClassInfo.run !Cmdline.out_dir;
    ConstantInfo.run !Cmdline.out_dir)

let analyze () = failwith "not implemented"

let synthesize () =
  L.info "Start synthesizing for %s" !Cmdline.target_program;
  if !Cmdline.test_case_ast then RunProgramAST.run !Cmdline.target_program
  else RunProgramDUG.run !Cmdline.target_program

let finalize t0 =
  L.info "Unitcon completes: %fs" (Sys.time () -. t0);
  L.finalize ()

let main () =
  let t0 = Sys.time () in
  Cmdline.parse ();
  (match !Cmdline.command with
  | Cmdline.Build -> build ()
  | Cmdline.Analyze -> analyze ()
  | Cmdline.Synthesize ->
      Sys.set_signal Sys.sigalrm RunProgram.normal_exit;
      synthesize ());
  finalize t0

let _ = main ()
