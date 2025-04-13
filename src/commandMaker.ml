open Utils

let manifest_file out_dir = Filename.(out_dir / "Manifest")

let dep_files out_dir = Filename.(out_dir / "jar-files")

let dependency_jar out_dir = Filename.(out_dir / "with-dependency.jar")

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ret = execute command in
  Sys.chdir current_dir;
  if ret <> 0 then failwith ("Faild to execute " ^ command)

(* Absolute path should be used instead of relative path *)
let rec collect_classpaths dir =
  if Sys.is_directory dir then
    Array.fold_left
      (fun acc file ->
        let abspath = Filename.(dir / file) |> Filename.resolve in
        if Sys.is_directory abspath then
          List.rev_append (collect_classpaths abspath) acc
        else if
          List.mem (Filename.extension file) [ ".jar"; ".class"; ".properties" ]
        then if String.contains abspath ' ' then acc else abspath :: acc
        else acc)
      [] (Sys.readdir dir)
  else []

let write_manifest_file oc paths =
  output_string oc "Class-Path: ";
  let rec write paths =
    match paths with
    | p :: tl when tl = [] ->
        output_string oc (p ^ "\n");
        write tl
    | p :: tl ->
        output_string oc (p ^ "\n  ");
        write tl
    | _ -> flush oc
  in
  write paths

let write_dep_files oc paths =
  let rec write paths =
    match paths with
    | p :: tl ->
        output_string oc (p ^ "\n");
        write tl
    | _ -> flush oc
  in
  write paths

let make_jar_with_dependencies p =
  let m_file = manifest_file !Cmdline.out_dir in
  let jar_files = dep_files !Cmdline.out_dir in
  let dep_jar = dependency_jar !Cmdline.out_dir in
  let manifest_oc = open_out m_file in
  let jar_files_oc = open_out jar_files in
  Filename.remove_file dep_jar;
  let abspaths = collect_classpaths p in
  write_manifest_file manifest_oc abspaths;
  write_dep_files jar_files_oc abspaths;
  close_out manifest_oc;
  close_out jar_files_oc;
  simple_compiler p ("jar -cmf " ^ m_file ^ " " ^ dep_jar ^ " @" ^ jar_files)

let execute_build_cmd p =
  let build_cmd_file = Filename.(Filename.(p / input_path) / "build-command") in
  let ic = open_in build_cmd_file in
  let cmds = read_all_string ic |> Str.split (Str.regexp "\n") in
  close_in ic;
  let rec execute cmds =
    match cmds with
    | c :: tl ->
        simple_compiler p c;
        execute tl
    | _ -> ()
  in
  execute cmds

let run p =
  execute_build_cmd p;
  make_jar_with_dependencies p
