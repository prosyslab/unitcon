module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module CallPropMap = Language.CallPropMap

let rm_exp exp str = Str.global_replace exp "" str

let rm_space str =
  let str = Str.replace_first (Str.regexp "^[ \t\r\n]+") "" str in
  Str.replace_first (Str.regexp "[ \t\r\n]+$") "" str

let parse_boitv boitv =
  let remove_bk str =
    Str.global_replace (Str.regexp "[{}]") "" str |> rm_space
  in
  let relation_list = remove_bk boitv |> Str.split (Str.regexp ",") in
  if List.length relation_list = 0 then Relation.M.empty
  else
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
              rm_exp (Str.regexp "max(") tail
              |> rm_exp (Str.regexp "min(")
              |> rm_exp (Str.regexp "[)\\[\\]]")
              |> rm_space
            in
            if check_relation head tail then Relation.M.add head tail mmap
            else mmap)
          mmap value_list)
      Relation.M.empty relation_list

let parse_citv citv =
  let remove_bk str = rm_exp (Str.regexp "[{}]") str |> rm_space in
  let value_list = remove_bk citv |> Str.split (Str.regexp ",") in
  if List.length value_list = 0 then Value.M.empty
  else
    List.fold_left
      (fun mmap mapping_value ->
        let mapping_value = Str.split (Str.regexp "->") mapping_value in
        let head = List.hd mapping_value |> rm_space in
        let tail = List.tl mapping_value |> List.hd |> rm_space in
        if Value.is_eq tail then
          let value = rm_exp (Str.regexp "=") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Eq (Int v)) mmap
          | None ->
              if value = "null" then Value.M.add head (Value.Eq Null) mmap
              else Value.M.add head (Value.Eq (String value)) mmap
        else if Value.is_neq tail then
          let value = rm_exp (Str.regexp "!=") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Neq (Int v)) mmap
          | None ->
              if value = "null" then Value.M.add head (Value.Neq Null) mmap
              else Value.M.add head (Value.Neq (String value)) mmap
        else if Value.is_ge tail then
          let value = rm_exp (Str.regexp ">=") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Ge (Int v)) mmap
          | None -> Value.M.add head (Value.Ge MinusInf) mmap
        else if Value.is_gt tail then
          let value = rm_exp (Str.regexp ">") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Gt (Int v)) mmap
          | None -> Value.M.add head (Value.Gt MinusInf) mmap
        else if Value.is_le tail then
          let value = rm_exp (Str.regexp "<=") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Le (Int v)) mmap
          | None -> Value.M.add head (Value.Le PlusInf) mmap
        else if Value.is_lt tail then
          let value = rm_exp (Str.regexp "<") tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Lt (Int v)) mmap
          | None -> Value.M.add head (Value.Lt PlusInf) mmap
        else if Value.is_between tail then
          let values =
            rm_exp (Str.regexp "in_N") tail
            |> rm_exp (Str.regexp "in\\[")
            |> rm_exp (Str.regexp "\\]")
            |> String.split_on_char ' '
          in
          if List.length values = 1 then
            Value.M.add head (Value.Between (MinusInf, PlusInf)) mmap
          else
            let min_value = List.hd values in
            let max_value = List.tl values |> List.hd in
            match int_of_string_opt min_value with
            | Some v1 -> (
                match int_of_string_opt max_value with
                | Some v2 ->
                    Value.M.add head (Value.Between (Int v1, Int v2)) mmap
                | None ->
                    if max_value = "null" then
                      Value.M.add head (Value.Between (Int v1, Int 0)) mmap
                    else Value.M.add head (Value.Between (Int v1, PlusInf)) mmap
                )
            | None -> (
                match int_of_string_opt max_value with
                | Some v2 ->
                    if min_value = "null" then
                      Value.M.add head (Value.Between (Int 0, Int v2)) mmap
                    else
                      Value.M.add head (Value.Between (MinusInf, Int v2)) mmap
                | None ->
                    if min_value = "null" then
                      Value.M.add head (Value.Between (Int 0, PlusInf)) mmap
                    else if max_value = "null" then
                      Value.M.add head (Value.Between (MinusInf, Int 0)) mmap
                    else
                      Value.M.add head (Value.Between (MinusInf, PlusInf)) mmap)
        else if Value.is_outside tail then
          let values =
            rm_exp (Str.regexp "not_in\\[") tail
            |> rm_exp (Str.regexp "\\]")
            |> String.split_on_char ' '
          in
          let min_value = List.hd values in
          let max_value = List.tl values |> List.hd in
          match int_of_string_opt min_value with
          | Some v1 -> (
              match int_of_string_opt max_value with
              | Some v2 ->
                  Value.M.add head (Value.Outside (Int v1, Int v2)) mmap
              | None ->
                  if max_value = "null" then
                    Value.M.add head (Value.Outside (Int v1, Int 0)) mmap
                  else Value.M.add head (Value.Outside (Int v1, PlusInf)) mmap)
          | None -> (
              match int_of_string_opt max_value with
              | Some v2 ->
                  if min_value = "null" then
                    Value.M.add head (Value.Outside (Int 0, Int v2)) mmap
                  else Value.M.add head (Value.Outside (MinusInf, Int v2)) mmap
              | None ->
                  if min_value = "null" then
                    Value.M.add head (Value.Outside (Int 0, PlusInf)) mmap
                  else if max_value = "null" then
                    Value.M.add head (Value.Outside (MinusInf, Int 0)) mmap
                  else Value.M.add head (Value.Outside (MinusInf, PlusInf)) mmap
              )
        else failwith "parse_citv error")
      Value.M.empty value_list

let parse_condition condition =
  let v_and_m = String.split_on_char ';' condition in
  let var_list =
    List.hd v_and_m
    |> Str.replace_first (Str.regexp "Stack=") ""
    |> rm_exp (Str.regexp "[&{}]")
    |> String.split_on_char ','
  in
  let mem =
    List.tl v_and_m |> List.hd
    |> Str.replace_first (Str.regexp "Heap=") ""
    |> rm_exp (Str.regexp "[{}]")
    |> String.split_on_char ','
  in
  let variables =
    List.fold_left
      (fun mmap var ->
        let i_and_s = String.split_on_char '=' var in
        let id = List.hd i_and_s |> rm_space in
        if String.length id = 0 then mmap
        else
          let symbol = List.tl i_and_s |> List.hd |> rm_space in
          Condition.M.add symbol (Condition.RH_Var id) mmap)
      Condition.M.empty var_list
  in
  let rec mk_ref_list ref_trace =
    match ref_trace with
    | hd :: tl ->
        let hd = rm_space hd in
        let check_symbol v = Str.string_match (Str.regexp "^v[0-9]+$") v 0 in
        if check_symbol hd then Condition.RH_Symbol hd :: mk_ref_list tl
        else Condition.RH_Var hd :: mk_ref_list tl
    | [] -> []
  in
  let memory =
    List.fold_left
      (fun mmap ref ->
        let ref_trace = Str.split (Str.regexp "->") ref in
        if List.length ref_trace = 0 then mmap
        else
          let head = List.hd ref_trace |> rm_space in
          let trace = List.tl ref_trace |> mk_ref_list in
          Condition.M.add head trace mmap)
      Condition.M.empty mem
  in
  (variables, memory)

let parse_args args = List.map (fun arg -> JsonUtil.to_string arg) args

let parse_callprop callprop =
  let relation =
    JsonUtil.member "BoItv" callprop |> JsonUtil.to_string |> parse_boitv
  in
  let value =
    JsonUtil.member "CItv" callprop |> JsonUtil.to_string |> parse_citv
  in
  let pre_var, pre_mem =
    JsonUtil.member "Precond" callprop |> JsonUtil.to_string |> parse_condition
  in
  let post_var, post_mem =
    JsonUtil.member "Postcond" callprop |> JsonUtil.to_string |> parse_condition
  in
  let args = JsonUtil.member "Arg" callprop |> JsonUtil.to_list |> parse_args in
  Language.
    {
      relation;
      value;
      precond = (pre_var, pre_mem);
      postcond = (post_var, post_mem);
      args;
    }

let get_method_names assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let caller_name =
    JsonUtil.member "Caller" assoc |> JsonUtil.to_string |> split_name
  in
  let callee_name =
    JsonUtil.member "Callee" assoc |> JsonUtil.to_string |> split_name
  in
  (caller_name, callee_name)

let mapping_callprop callprop mmap =
  let method_names = get_method_names callprop in
  let callprop = parse_callprop callprop in
  let callprop_map =
    match CallPropMap.M.find_opt method_names mmap with
    | Some props -> CallPropMap.M.add method_names (callprop :: props) mmap
    | None -> CallPropMap.M.add method_names [ callprop ] mmap
  in
  callprop_map

let from_callprop_json json =
  List.fold_left
    (fun mmap callprop -> mapping_callprop callprop mmap)
    CallPropMap.M.empty json
