let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  (try Unix.mkdir (!Cmdline.out_dir ^ "/marshal") 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir)

let main () =
  let usage = "Usage: unitcon [options] [target_program]" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  ignore (Unix.alarm !Cmdline.time_out);
  match !Cmdline.target_program with
  | None -> failwith "Error: Target Program is not given"
  | Some p when !Cmdline.class_info ->
      initialize ();
      ClassInfo.run p
  | Some p when !Cmdline.constant_info ->
      initialize ();
      ConstantInfo.run p
  | Some p ->
      initialize ();
      if !Cmdline.test_case_ast then RunProgramAST.run p
      else RunProgramDUG.run p

let _ =
  Sys.set_signal Sys.sigalrm RunProgram.normal_exit;
  main ()
