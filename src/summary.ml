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

let parse_param param =
  let v_and_t = String.split_on_char ':' param in
  let get_type t =
    match t with
    | "int" -> Language.Int
    | "float" -> Language.Float
    | "String" -> Language.String
    | "" -> Language.None
    | _ ->
        let class_name = String.split_on_char '.' t |> List.rev |> List.hd in
        let class_name = Str.replace_first (Str.regexp "*") "" class_name in
        Language.Object class_name
  in
  if List.length v_and_t = 1 then Language.Var (get_type "", "")
  else
    let mk_variable var typ =
      if var = "this" then Language.This (get_type typ)
      else Language.Var (get_type typ, var)
    in
    let var = List.hd v_and_t in
    let typ = List.tl v_and_t |> List.hd in
    mk_variable var typ

let parse_boitv boitv =
  let remove_bk str = Str.global_replace (Str.regexp "[{}]") "" str in
  let relation_list = remove_bk boitv |> Str.split (Str.regexp ", v") in
  let relation_list =
    if List.length relation_list = 1 then relation_list
    else
      List.hd relation_list
      :: (List.tl relation_list |> List.map (fun elem -> "v" ^ elem))
  in
  List.fold_left
    (fun mmap relation ->
      let relation = Str.split (Str.regexp "->") relation in
      let check_relation head tail =
        match int_of_string_opt tail with
        | Some _ -> false
        | None -> if head = tail then false else true
      in
      let head = List.hd relation |> rm_space in
      let tail = List.tl relation |> List.hd |> rm_space in
      if check_relation head tail then Relation.M.add head tail mmap else mmap)
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

let get_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_name
  in
  method_name

let mapping_method_info method_info mmap =
  let method_name = get_method_name method_info in
  let modifier =
    JsonUtil.member "modifier" method_info |> Language.modifier_of_json
  in
  let formal_params =
    JsonUtil.member "param" method_info
    |> JsonUtil.to_list
    |> List.map (fun param -> JsonUtil.to_string param |> parse_param)
  in
  let filename =
    JsonUtil.member "filename" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let info = MethodInfo.{ modifier; formal_params; filename } in
  MethodInfo.M.add method_name info mmap

let mapping_summary method_summarys mmap =
  let method_name = get_method_name method_summarys in
  let summarys =
    JsonUtil.member "summary" method_summarys
    |> JsonUtil.to_list
    |> List.map (fun summary -> parse_summary summary)
  in
  let summarys =
    if summarys = [] then
      [
        Language.
          {
            relation = Relation.M.empty;
            value = [];
            precond = (Condition.M.empty, Condition.M.empty);
            postcond = (Condition.M.empty, Condition.M.empty);
          };
      ]
    else summarys
  in
  SummaryMap.M.add method_name summarys mmap

let from_method_json json =
  List.fold_left
    (fun mmap method_info -> mapping_method_info method_info mmap)
    MethodInfo.M.empty json

let from_summary_json json =
  List.fold_left
    (fun mmap method_summarys -> mapping_summary method_summarys mmap)
    SummaryMap.M.empty json
