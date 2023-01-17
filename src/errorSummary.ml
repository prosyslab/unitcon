module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap

let rm_exp exp str = Str.global_replace exp "" str

let rm_space str =
  let str = Str.replace_first (Str.regexp "^[ \t\r\n]+") "" str in
  Str.replace_first (Str.regexp "[ \t\r\n]+$") "" str

let parse_boitv boitv =
  let remove_bk str = Str.global_replace (Str.regexp "[{}]") "" str in
  let relation_list = remove_bk boitv |> Str.split (Str.regexp ",") in
  List.fold_left
    (fun mmap relation ->
      let relation = Str.split (Str.regexp "->") relation in
      let check_relation head tail =
        match int_of_string_opt tail with
        | Some _ -> false
        | None -> if head = tail then false else true
      in
      let head = List.hd relation |> rm_space in
      let value_list =
        List.tl relation |> List.hd |> String.split_on_char ' '
      in
      List.fold_left
        (fun mmap tail ->
          let tail =
            rm_exp (Str.regexp "[max|min|(|)|\\[|\\]]") tail |> rm_space
          in
          if check_relation head tail then Relation.M.add head tail mmap
          else mmap)
        mmap value_list)
    Relation.M.empty relation_list

let parse_citv citv =
  let remove_bk str = rm_exp (Str.regexp "[{}]") str in
  let value_list = remove_bk citv |> String.split_on_char ',' in
  List.map
    (fun mapping_value ->
      let mapping_value = Str.split (Str.regexp "->") mapping_value in
      let head = List.hd mapping_value |> rm_space in
      let tail = List.tl mapping_value |> List.hd |> rm_space in
      if Value.is_eq tail then
        let value = rm_exp (Str.regexp "=") tail in
        match int_of_string_opt value with
        | Some v -> Value.Eq (head, Int v)
        | None ->
            if value = "null" then Value.Eq (head, Null)
            else Value.Eq (head, String value)
      else if Value.is_neq tail then
        let value = rm_exp (Str.regexp "!=") tail in
        match int_of_string_opt value with
        | Some v -> Value.Neq (head, Int v)
        | None ->
            if value = "null" then Value.Neq (head, Null)
            else Value.Neq (head, String value)
      else if Value.is_ge tail then
        let value = rm_exp (Str.regexp ">=") tail in
        match int_of_string_opt value with
        | Some v -> Value.Ge (head, Int v)
        | None -> failwith ("Ge: " ^ value)
      else if Value.is_gt tail then
        let value = rm_exp (Str.regexp ">") tail in
        match int_of_string_opt value with
        | Some v -> Value.Gt (head, Int v)
        | None -> failwith ("Gt: " ^ value)
      else if Value.is_le tail then
        let value = rm_exp (Str.regexp "<=") tail in
        match int_of_string_opt value with
        | Some v -> Value.Le (head, Int v)
        | None -> failwith ("Le: " ^ value)
      else if Value.is_lt tail then
        let value = rm_exp (Str.regexp "<") tail in
        match int_of_string_opt value with
        | Some v -> Value.Lt (head, Int v)
        | None -> failwith ("Lt: " ^ value)
      else if Value.is_between tail then
        let values =
          rm_exp (Str.regexp "(in_N)|(in[\\[\\]])") tail
          |> String.split_on_char ' '
        in
        let min_value = List.hd values in
        let max_value = List.tl values |> List.hd in
        match int_of_string_opt min_value with
        | Some v -> Value.Between (head, Int v, Int (int_of_string max_value))
        | None -> Value.Between (head, MinusInf, PlusInf)
      else if Value.is_outside tail then
        let values =
          rm_exp (Str.regexp "not_in[\\[\\]]") tail |> String.split_on_char ' '
        in
        let min_value = List.hd values in
        let max_value = List.tl values |> List.hd in
        match int_of_string_opt min_value with
        | Some v -> Value.Outside (head, Int v, Int (int_of_string max_value))
        | None -> failwith ("Outside: " ^ min_value)
      else failwith "parse_citv error")
    value_list

let parse_condition condition =
  let v_and_m = String.split_on_char ';' condition in
  let var_list =
    List.hd v_and_m
    |> rm_exp (Str.regexp "Stack=")
    |> rm_exp (Str.regexp "[&{}]")
    |> String.split_on_char ','
  in
  let mem =
    List.tl v_and_m |> List.hd
    |> rm_exp (Str.regexp "Heap=")
    |> rm_exp (Str.regexp "[ {}]")
    |> String.split_on_char ','
  in
  let variables =
    List.fold_left
      (fun mmap var ->
        let i_and_s = String.split_on_char '=' var in
        let id = List.hd i_and_s in
        let symbol = List.tl i_and_s |> List.hd in
        Condition.M.add symbol (Condition.RH_Var id) mmap)
      Condition.M.empty var_list
  in
  let rec mk_ref_list ref_trace =
    match ref_trace with
    | hd :: tl ->
        let check_symbol v = Str.string_match (Str.regexp "^v[0-9]$") v 0 in
        if check_symbol hd then Condition.RH_Symbol hd :: mk_ref_list tl
        else Condition.RH_Var hd :: mk_ref_list tl
    | [] -> []
  in
  let memory =
    List.fold_left
      (fun mmap ref ->
        let ref_trace = Str.split (Str.regexp "->") ref in
        let head = List.hd ref_trace in
        let trace = List.tl ref_trace |> mk_ref_list in
        Condition.M.add head trace mmap)
      Condition.M.empty mem
  in
  (variables, memory)

let parse_summary summary =
  let relation =
    JsonUtil.member "BoItv" summary |> JsonUtil.to_string |> parse_boitv
  in
  let value =
    JsonUtil.member "CItv" summary |> JsonUtil.to_string |> parse_citv
  in
  let pre_var, pre_mem =
    JsonUtil.member "Precond" summary |> JsonUtil.to_string |> parse_condition
  in
  let post_var, post_mem =
    JsonUtil.member "Postcond" summary |> JsonUtil.to_string |> parse_condition
  in
  Language.
    {
      relation;
      value;
      precond = (pre_var, pre_mem);
      postcond = (post_var, post_mem);
    }

let mapping_error_summary source_method error_summary mmap =
  let summary = parse_summary error_summary in
  SummaryMap.M.add source_method summary mmap

let from_error_summary_json source_method json =
  List.fold_left
    (fun mmap error_summary ->
      mapping_error_summary source_method error_summary mmap)
    SummaryMap.M.empty json

let get_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "method" assoc |> JsonUtil.to_string |> split_name
  in
  method_name

let source_method json = JsonUtil.to_list json |> List.hd |> get_method_name
