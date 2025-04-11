open Language
open RunProgram
open Dug
module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

let insert_loop loop_id =
  let lval = DUG.loop_id_lval_code loop_id in
  let id = snd lval in
  let index = id ^ "_index" in
  let init = index ^ " = 0; " in
  let cond = index ^ " < " ^ id ^ "_comb.length; " in
  let incr = index ^ "++" in
  "for(int " ^ init ^ cond ^ incr ^ ") {\n"

let insert_loops loop_id_map =
  LoopIdMap.M.fold
    (fun id _ (code, count) -> (code ^ insert_loop id, count + 1))
    loop_id_map ("", 0)

let check_same_loop (_, tc) loop_id_map =
  let tc_list = String.split_on_char '\n' tc in
  let found_id id line =
    match Str.search_forward (Str.regexp ("[( ]" ^ id ^ "[^0-9]")) line 0 with
    | exception Not_found -> false
    | _ -> true
  in
  let found_id_pair typ id_code exps prev_ids acc =
    List.fold_left
      (fun ids (o_typ, o_id_code, o_exps) ->
        if o_typ = typ && o_exps = exps then (id_code, o_id_code) :: ids
        else ids)
      acc prev_ids
  in
  let duplicated_list =
    LoopIdMap.M.fold
      (fun id exps (ids, prev_ids) ->
        let typ, id_code = DUG.loop_id_lval_for_check id in
        if typ = NonType || id_code = "" then (ids, prev_ids)
        else
          let ids = found_id_pair typ id_code exps prev_ids ids in
          (ids, (typ, id_code, exps) :: prev_ids))
      loop_id_map ([], [])
    |> fst
  in
  if duplicated_list = [] then false
  else
    List.fold_left
      (fun check line ->
        List.fold_left
          (fun check (id1, id2) ->
            let found_id1 = found_id id1 line in
            let found_id2 = found_id id2 line in
            if found_id1 && found_id2 then false else check)
          check duplicated_list)
      true tc_list

let array_for_loop loop_id_map =
  LoopIdMap.M.fold
    (fun id exps code -> code ^ DUG.loop_id_code id exps)
    loop_id_map ""

let insert_multi_test_log loop_id_map =
  let end_signal = "System.err.println(\"-----LogEnd-----\");\n" in
  let log lval =
    let id = snd lval in
    if is_primitive (fst lval) then
      "System.err.println(\"Log=\" + \"" ^ id ^ "\" + \"=\" + " ^ id ^ "_comb["
      ^ id ^ "_index" ^ "]" ^ ");\n"
    else
      "System.err.println(\"Log=\" + \"" ^ id ^ "\" + \"=\" + " ^ id
      ^ "_string_comb[" ^ id ^ "_index" ^ "]" ^ ");\n"
  in
  LoopIdMap.M.fold
    (fun id _ code -> log (DUG.loop_id_lval_code id) ^ code)
    loop_id_map end_signal

let get_code_for_loop loop_id_map =
  let arrays = array_for_loop loop_id_map in
  let loop_stmt, loop_cnt = insert_loops loop_id_map in
  let loop_input_log = insert_multi_test_log loop_id_map in
  (arrays, loop_stmt, loop_cnt, loop_input_log)

let str_to_primitive v value =
  match DUG.get_vinfo v |> fst with
  | Int | Long | Short | Byte -> DUGIR.Primitive (Z (int_of_string value))
  | Float | Double -> DUGIR.Primitive (R (float_of_string value))
  | Bool -> DUGIR.Primitive (B (bool_of_string value))
  | Char -> DUGIR.Primitive (C value.[0])
  | String -> if value = "null" then DUGIR.Null else DUGIR.Primitive (S value)
  | Object _ ->
      if value = "null" then DUGIR.Null else DUGIR.GlobalConstant value
  | _ -> failwith "Fail: convert string to primitive"

let get_id_to_be_modified v id =
  (* array_id, index_id *)
  match DUG.get_vinfo v |> fst with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String | Object _
    ->
      (id ^ "_comb", id ^ "_index")
  | _ -> failwith "Fail: get id to be modified"

let loop_value_to_tc rep_input loop_id_map tc =
  let find_id str_id =
    LoopIdMap.M.fold
      (fun id _ found ->
        if str_id = (DUG.loop_id_lval_code id |> snd) then id else found)
      loop_id_map DUGIR.Id
  in
  List.fold_left
    (fun old_tc (id, value) ->
      let ast_id = find_id id in
      let array_id, index_id = get_id_to_be_modified ast_id id in
      let to_be_modified = array_id ^ "\\[" ^ index_id ^ "\\]" in
      let real_input = str_to_primitive ast_id value in
      let input_code = DUG.exp_code real_input ast_id in
      let x = Str.replace_first (Str.regexp to_be_modified) input_code old_tc in
      Str.global_replace (Str.regexp "\\") "\\\\\\\\" x)
    tc rep_input

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info p_data =
  GeneratorDUG.mk_testcases ~is_start queue e_method_info p_data

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start info queue e_method_info p_data =
  if !normal_exit_flag then raise Normal_Exit
  else if !early_stop_flag then raise Early_Stop
  else run_test_when_no_exn ~is_start info queue e_method_info p_data

and run_test_when_no_exn ~is_start info queue e_method_info p_data =
  let completion, tc, loop_id_map, tc_list =
    make_testcase ~is_start queue e_method_info p_data
  in
  if completion = Need_Loop then (
    (* clean before executing multi tests *)
    remove_all_files info.multi_test_dir;
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_multi_tc_files;
    let loop_info = get_code_for_loop loop_id_map in
    let check_duplicated =
      if !Cmdline.unknown_bug then check_same_loop tc loop_id_map else false
    in
    let found_rep_input =
      if check_duplicated then []
      else (
        add_multi_testcase info.multi_test_dir !num_of_multi_tc_files
          (tc, loop_info, _time);
        run_multi_testfile ())
    in
    if found_rep_input = [] then
      run_test ~is_start:false info tc_list e_method_info p_data
    else
      (* found crash input with loop *)
      let new_tc = loop_value_to_tc found_rep_input loop_id_map (tc |> snd) in
      let _time = Unix.gettimeofday () -. !time in
      incr num_of_tc_files;
      add_testcase info.test_dir !num_of_tc_files ((tc |> fst, new_tc), _time);
      if !num_of_tc_files mod !Cmdline.batch_size = 0 || !early_stop_keep_going
      then run_testfile ()
      else ();
      run_test ~is_start:false info tc_list e_method_info p_data)
  else if completion = Incomplete then (
    (* early stopping *)
    if !num_of_last_exec_tc < !num_of_tc_files then run_testfile () else ();
    raise Normal_Exit)
  else
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_tc_files;
    add_testcase info.test_dir !num_of_tc_files (tc, _time);
    if !num_of_tc_files mod !Cmdline.batch_size = 0 then run_testfile () else ();
    run_test ~is_start:false info tc_list e_method_info p_data

let run program_dir out_dir =
  try
    let error_method_info, p_data = setup program_dir out_dir in
    run_test ~is_start:true !info [] error_method_info p_data
  with
  | Normal_Exit ->
      Logger.info "Catch Normal Exit exception in RunProgramDUG";
      normal_exit (Unix.gettimeofday ())
  | Early_Stop ->
      Logger.info "Catch Early Stop exception in RunProgramDUG";
      early_run_test (Unix.gettimeofday ())
