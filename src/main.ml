let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  (try Unix.mkdir (!Cmdline.out_dir ^ "/marshal") 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir)

let main () =
  let usage = "Usage: unitcon [options] [target_program]" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  match !Cmdline.target_program with
  | None -> failwith "Error: Target Program is not given"
  | Some p ->
      initialize ();
      RunProgram.run p

let _ =
  let stopit =
    Sys.Signal_handle
      (fun _ ->
        print_endline "time-out";
        Unix._exit 0)
  in
  Sys.set_signal Sys.sigalrm stopit;
  ignore (Unix.alarm !Cmdline.time_out);
  main ()
