module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap

let mk_rh_type v =
  let check_symbol v = Str.string_match Regexp.symbol v 0 in
  let check_index v = Str.string_match Regexp.index v 0 in
  let check_any_value v = Str.string_match Regexp.any v 0 in
  if check_symbol v then Condition.RH_Symbol v
  else if check_index v then
    Condition.RH_Index
      (v |> Regexp.first_rm Regexp.open_bk |> Regexp.first_rm Regexp.end_bk)
  else if check_any_value v then Condition.RH_Any
  else Condition.RH_Var v

let parse_param param =
  let v_and_t = String.split_on_char ':' param in
  let rec get_type t =
    match t with
    | "int" | "signed short" -> ("", Language.Int)
    | "long" -> ("", Language.Long)
    | "float" -> ("", Language.Float)
    | "double" -> ("", Language.Double)
    | "_Bool" | "boolean" -> ("", Language.Bool)
    | "unsigned short" | "signed char" | "unsigned char" -> ("", Language.Char)
    | "java.lang.String*" -> ("java.lang.String", Language.String)
    | "" -> ("", Language.None)
    | _ when Str.string_match Regexp.array t 0 ->
        let _, typ = t |> Regexp.first_rm Regexp.rm_array |> get_type in
        ("", Language.Array typ)
    | _ ->
        let import = Regexp.global_rm (Str.regexp "\\*.*$") t in
        let class_name = String.split_on_char '.' t |> List.rev |> List.hd in
        let class_name = Regexp.first_rm Regexp.any class_name in
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
  let relation_list = Regexp.remove_bk boitv |> Str.split Regexp.bm in
  if relation_list = [] then Relation.M.empty
  else
    List.fold_left
      (fun mmap relation ->
        let relation = Str.split Regexp.arrow relation in
        let check_relation head tail =
          match int_of_string_opt tail with
          | Some _ -> false
          | None -> if head = tail then false else true
        in
        let head = List.hd relation |> Regexp.rm_space in
        let value_list =
          List.tl relation |> List.hd |> String.split_on_char ' '
        in
        List.fold_left
          (fun mmap tail ->
            let tail =
              Regexp.first_rm Regexp.max tail
              |> Regexp.first_rm Regexp.min
              |> Regexp.global_rm Regexp.bk2
              |> Regexp.rm_space
            in
            if check_relation head tail then Relation.M.add head tail mmap
            else mmap)
          mmap value_list)
      Relation.M.empty relation_list

let parse_citv citv =
  let value_list = Regexp.remove_bk citv |> Str.split Regexp.bm in
  if value_list = [] then Value.M.empty
  else
    List.fold_left
      (fun mmap mapping_value ->
        let mapping_value = Str.split Regexp.arrow mapping_value in
        let head = List.hd mapping_value |> Regexp.rm_space in
        let tail = List.tl mapping_value |> List.hd |> Regexp.rm_space in
        if Value.is_eq tail then
          let value = Regexp.first_rm Regexp.eq tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Eq (Int v)) mmap
          | None ->
              if value = "null" then Value.M.add head (Value.Eq Null) mmap
              else Value.M.add head (Value.Eq (String value)) mmap
        else if Value.is_neq tail then
          let value = Regexp.first_rm Regexp.neq tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Neq (Int v)) mmap
          | None ->
              if value = "null" then Value.M.add head (Value.Neq Null) mmap
              else Value.M.add head (Value.Neq (String value)) mmap
        else if Value.is_ge tail then
          let value = Regexp.first_rm Regexp.ge tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Ge (Int v)) mmap
          | None -> Value.M.add head (Value.Ge MinusInf) mmap
        else if Value.is_gt tail then
          let value = Regexp.first_rm Regexp.gt tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Gt (Int v)) mmap
          | None -> Value.M.add head (Value.Gt MinusInf) mmap
        else if Value.is_le tail then
          let value = Regexp.first_rm Regexp.le tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Le (Int v)) mmap
          | None -> Value.M.add head (Value.Le PlusInf) mmap
        else if Value.is_lt tail then
          let value = Regexp.first_rm Regexp.lt tail in
          match int_of_string_opt value with
          | Some v -> Value.M.add head (Value.Lt (Int v)) mmap
          | None -> Value.M.add head (Value.Lt PlusInf) mmap
        else if Value.is_between tail then
          let values =
            Regexp.first_rm Regexp.in_n tail
            |> Regexp.first_rm Regexp.in_bk
            |> Regexp.first_rm Regexp.end_bk
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
            Regexp.first_rm Regexp.ots tail
            |> Regexp.first_rm Regexp.end_bk
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
  if List.length v_and_m < 2 then (Condition.M.empty, Condition.M.empty)
  else
    let var_list =
      List.hd v_and_m
      |> Regexp.first_rm Regexp.stack
      |> Regexp.global_rm Regexp.remain_symbol
      |> String.split_on_char ','
    in
    let mem =
      List.tl v_and_m |> List.hd
      |> Regexp.first_rm Regexp.heap
      |> Regexp.global_rm Regexp.remain_symbol2
      |> Regexp.global_rm Regexp.o_bk
      |> Regexp.rm_space |> Str.split Regexp.c_bk
    in
    let variables =
      List.fold_left
        (fun mmap var ->
          let i_and_s = String.split_on_char '=' var in
          let id = List.hd i_and_s |> Regexp.rm_space in
          if String.length id = 0 then mmap
          else
            let symbol = List.tl i_and_s |> List.hd |> Regexp.rm_space in
            Condition.M.add (symbol |> mk_rh_type) (Condition.RH_Var id) mmap)
        Condition.M.empty var_list
    in
    let rec mk_ref_map ref_trace mmap =
      match ref_trace with
      | hd :: tl -> (
          if hd |> Regexp.rm_space = "" then mmap
          else
            let ref = Str.split (Str.regexp "->") hd in
            try
              let field = List.hd ref |> Regexp.rm_space |> mk_rh_type in
              let value =
                List.tl ref |> List.hd |> Regexp.rm_space |> mk_rh_type
              in
              Condition.M.add field value mmap |> mk_ref_map tl
            with _ -> mk_ref_map tl mmap)
      | [] -> mmap
    in
    let memory =
      List.fold_left
        (fun mmap ref ->
          let ref_trace =
            Regexp.global_rm Regexp.start_bm ref
            |> Regexp.rm_space |> Str.split Regexp.bm
          in
          if ref_trace = [] || Str.string_match Regexp.ref (List.hd ref_trace) 0
          then mmap
          else
            let head =
              List.hd ref_trace |> Str.split Regexp.arrow |> List.hd
              |> Regexp.rm_space
            in
            let partial_tl =
              List.hd ref_trace
              |> Regexp.global_rm ("^" ^ head ^ "[ \t\r\n]+->" |> Str.regexp)
              |> Regexp.rm_space
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

let get_return assoc =
  let split_return m =
    if String.contains m ' ' then m |> String.split_on_char ' ' |> List.hd
    else ""
  in
  let return =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_return
  in
  return

let mapping_method_info method_info mmap =
  let method_name = get_method_name method_info in
  let return = get_return method_info in
  let modifier =
    JsonUtil.member "modifier" method_info
    |> JsonUtil.to_list |> List.hd |> Language.modifier_of_json
  in
  let is_static =
    JsonUtil.member "is_static" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> bool_of_string
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
  let info =
    MethodInfo.{ modifier; is_static; formal_params; return; filename }
  in
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
  let json = JsonUtil.to_list json in
  let method_info =
    List.fold_left
      (fun mmap method_info -> mapping_method_info method_info mmap)
      MethodInfo.M.empty json
  in
  Modeling.add_java_package_method method_info

let from_summary_json json =
  let json = JsonUtil.to_list json in
  let summary_map =
    List.fold_left
      (fun mmap method_summarys -> mapping_summary method_summarys mmap)
      SummaryMap.M.empty json
  in
  Modeling.add_java_package_summary summary_map
