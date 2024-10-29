open Language
open RunProgram
open Ast
module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

let insert_loop loop_id =
  let lval = AST.loop_id_lval_code loop_id in
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

let array_for_loop loop_id_map =
  LoopIdMap.M.fold
    (fun id exps code -> code ^ AST.loop_id_code id exps)
    loop_id_map ""

let insert_multi_test_log loop_id_map =
  let end_signal = "System.err.println(\"-----LogEnd-----\");\n" in
  let log lval =
    let id = snd lval in
    "System.err.println(\"Log=\" + \"" ^ id ^ "\" + \"=\" + " ^ id ^ "_comb["
    ^ id ^ "_index" ^ "]" ^ ");\n"
  in
  LoopIdMap.M.fold
    (fun id _ code -> log (AST.loop_id_lval_code id) ^ code)
    loop_id_map end_signal

let get_code_for_loop loop_id_map =
  let arrays = array_for_loop loop_id_map in
  let loop_stmt, loop_cnt = insert_loops loop_id_map in
  let loop_input_log = insert_multi_test_log loop_id_map in
  (arrays, loop_stmt, loop_cnt, loop_input_log)

let str_to_primitive v value =
  match AST.get_vinfo v |> fst with
  | Int | Long | Short | Byte -> ASTIR.Primitive (Z (int_of_string value))
  | Float | Double -> ASTIR.Primitive (R (float_of_string value))
  | Bool -> ASTIR.Primitive (B (bool_of_string value))
  | Char -> ASTIR.Primitive (C value.[0])
  | String -> if value = "null" then ASTIR.Null else ASTIR.Primitive (S value)
  | _ -> failwith "Fail: convert string to primitive"

let get_id_to_be_modified v id =
  (* array_id, index_id *)
  match AST.get_vinfo v |> fst with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String ->
      (id ^ "_comb", id ^ "_index")
  | _ -> failwith "Fail: get id to be modified"

let loop_value_to_tc rep_input loop_id_map tc =
  let find_id str_id =
    LoopIdMap.M.fold
      (fun id _ found ->
        if str_id = (AST.loop_id_lval_code id |> snd) then id else found)
      loop_id_map Id
  in
  List.fold_left
    (fun old_tc (id, value) ->
      let ast_id = find_id id in
      let array_id, index_id = get_id_to_be_modified ast_id id in
      let to_be_modified = array_id ^ "\\[" ^ index_id ^ "\\]" in
      let real_input = str_to_primitive ast_id value in
      let input_code = AST.exp_code real_input ast_id in
      Str.replace_first (Str.regexp to_be_modified) input_code old_tc)
    tc rep_input

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info program_info =
  GeneratorAST.mk_testcases ~is_start queue e_method_info program_info

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start info queue e_method_info p_data =
  let completion, tc, loop_id_map, tc_list =
    make_testcase ~is_start queue e_method_info p_data
  in
  if completion = Need_Loop then (
    (* clean before executing multi tests *)
    remove_all_files info.multi_test_dir;
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_multi_tc_files;
    let loop_info = get_code_for_loop loop_id_map in
    add_multi_testcase info.multi_test_dir !num_of_multi_tc_files
      (tc, loop_info, _time);
    let found_rep_input = run_multi_testfile () in
    if found_rep_input = [] then
      run_test ~is_start:false info tc_list e_method_info p_data
    else
      (* found crash input with loop *)
      let new_tc = loop_value_to_tc found_rep_input loop_id_map (tc |> snd) in
      let _time = Unix.gettimeofday () -. !time in
      incr num_of_tc_files;
      add_testcase info.test_dir !num_of_tc_files ((tc |> fst, new_tc), _time);
      if !num_of_tc_files mod 15 = 0 || !abnormal_keep_going then
        run_testfile ()
      else ();
      run_test ~is_start:false info tc_list e_method_info p_data)
  else if completion = Incomplete then (
    (* early stopping *)
    if !num_of_last_exec_tc < !num_of_tc_files then run_testfile () else ();
    Unix.kill (Unix.getpid ()) Sys.sigusr1)
  else
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_tc_files;
    add_testcase info.test_dir !num_of_tc_files (tc, _time);
    if !num_of_tc_files mod 15 = 0 then run_testfile () else ();
    run_test ~is_start:false info tc_list e_method_info p_data

let run program_dir =
  let error_method_info, p_data = setup program_dir in
  run_test ~is_start:true !info [] error_method_info p_data
