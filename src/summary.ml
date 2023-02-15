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
  let rec get_type t =
    match t with
    | "int" | "signed short" | "long" -> ("", Language.Int)
    | "float" | "double" -> ("", Language.Float)
    | "_Bool" | "boolean" -> ("", Language.Bool)
    | "unsigned short" | "signed char" | "unsigned char" -> ("", Language.Char)
    | "java.lang.String*" -> ("java.lang.String", Language.String)
    | "" -> ("", Language.None)
    | _ when Str.string_match (Str.regexp ".+\\[_\\*_\\].*") t 0 ->
        let import, typ =
          t |> Str.replace_first (Str.regexp "\\[_\\*_\\](\\*)") "" |> get_type
        in
        (import, Language.Array typ)
    | _ ->
        let import = rm_exp (Str.regexp "\\*.*$") t in
        let class_name = String.split_on_char '.' t |> List.rev |> List.hd in
        let class_name = Str.replace_first (Str.regexp "*") "" class_name in
        (import, Language.Object class_name)
  in
  if List.length v_and_t = 1 then ("", Language.Var (None, ""))
  else
    let mk_variable var typ =
      if var = "this" then
        let import, typ = get_type typ in
        (import, Language.This typ)
      else
        let import, typ = get_type typ in
        (import, Language.Var (typ, var))
    in
    let var = List.hd v_and_t in
    let typ = List.tl v_and_t |> List.hd in
    mk_variable var typ

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
    |> rm_exp (Str.regexp "}*[ \t\r\n]+}$")
    |> rm_exp (Str.regexp "{")
    |> rm_space
    |> Str.split (Str.regexp "}")
  in
  let mk_rh_type v =
    let check_symbol v = Str.string_match (Str.regexp "^v[0-9]+$") v 0 in
    let check_index v = Str.string_match (Str.regexp "^\\[v[0-9]+\\]$") v 0 in
    let check_any_value v = Str.string_match (Str.regexp "\\*") v 0 in
    if check_symbol v then Condition.RH_Symbol v
    else if check_index v then Condition.RH_Index v
    else if check_any_value v then Condition.RH_Any
    else Condition.RH_Var v
  in
  let variables =
    List.fold_left
      (fun mmap var ->
        let i_and_s = String.split_on_char '=' var in
        let id = List.hd i_and_s |> rm_space in
        if String.length id = 0 then mmap
        else
          let symbol = List.tl i_and_s |> List.hd |> rm_space in
          Condition.M.add (symbol |> mk_rh_type) (Condition.RH_Var id) mmap)
      Condition.M.empty var_list
  in
  let rec mk_ref_map ref_trace mmap =
    match ref_trace with
    | hd :: tl -> (
        if hd |> rm_space = "" then mmap
        else
          let ref = Str.split (Str.regexp "->") hd in
          try
            let field = List.hd ref |> rm_space |> mk_rh_type in
            let value = List.tl ref |> List.hd |> rm_space |> mk_rh_type in
            Condition.M.add field value mmap |> mk_ref_map tl
          with _ -> mk_ref_map tl mmap)
    | [] -> mmap
  in
  let memory =
    List.fold_left
      (fun mmap ref ->
        let ref_trace =
          rm_exp (Str.regexp "^,[ \t\r\n]*") ref
          |> rm_space
          |> Str.split (Str.regexp ",")
        in
        if List.length ref_trace = 0 then mmap
        else
          let head =
            List.hd ref_trace
            |> Str.split (Str.regexp "->")
            |> List.hd |> rm_space
          in
          let partial_tl =
            List.hd ref_trace
            |> rm_exp ("^" ^ head ^ "[ \t\r\n]+->" |> Str.regexp)
            |> rm_space
          in
          let trace = List.tl ref_trace |> List.cons partial_tl in
          let trace = mk_ref_map trace Condition.M.empty in
          Condition.M.add (head |> mk_rh_type) trace mmap)
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
      args = [];
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
    JsonUtil.member "modifier" method_info
    |> JsonUtil.to_list |> List.hd |> Language.modifier_of_json
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
    if summarys = [] then [ Language.empty_summary ] else summarys
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
