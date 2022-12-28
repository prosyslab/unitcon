module Method = Language.Method
module MethodMap = Language.MethodMap
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module Exp = Summary.Exp
module Procname = Summary.Procname
module PredSymb = Summary.PredSymb
module Predicate = Summary.Predicate
module Memory = Summary.Memory

type prop = Memory.t

type t = { prop : prop }

type error_summary = t list

module ErrorSummaryMap = struct
  module M = Map.Make (struct
    type t = Method.t

    let compare = compare
  end)

  type t = error_summary M.t
end

let is_le str = String.contains str '<' && String.contains str '='

let is_lt str = String.contains str '<'

let is_ge str = String.contains str '>' && String.contains str '='

let is_gt str = String.contains str '>'

let is_neq str = String.contains str '!' && String.contains str '='

let is_eq str = String.contains str '='

let rec mk_exp exp =
  let exp = Str.replace_first (Str.regexp ":") "" exp in
  try Exp.Int (int_of_string exp)
  with _ -> (
    match exp with
    | _ when String.contains exp '+' ->
        let exp_list = String.split_on_char '+' exp in
        Exp.Plus
          ( exp_list |> List.hd |> String.trim |> mk_exp,
            exp_list |> List.tl |> List.hd |> String.trim |> mk_exp )
    | _ when String.contains exp '-' ->
        let exp_list = String.split_on_char '-' exp in
        Exp.Minus
          ( exp_list |> List.hd |> String.trim |> mk_exp,
            exp_list |> List.tl |> List.hd |> String.trim |> mk_exp )
    | _ when String.contains exp '*' ->
        let exp_list = String.split_on_char '*' exp in
        Exp.Mul
          ( exp_list |> List.hd |> String.trim |> mk_exp,
            exp_list |> List.tl |> List.hd |> String.trim |> mk_exp )
    | _ when String.contains exp '/' ->
        let exp_list = String.split_on_char '/' exp in
        Exp.Div
          ( exp_list |> List.hd |> String.trim |> mk_exp,
            exp_list |> List.tl |> List.hd |> String.trim |> mk_exp )
    | _ ->
        let regexp1 = Str.regexp_string "val$" in
        let regrexp2 = Str.regexp_string "@f$" in
        if Str.string_match regexp1 exp 0 || Str.string_match regrexp2 exp 0
        then Exp.Symbol exp
        else Exp.Var exp)

let mk_field element =
  let var_and_value = String.split_on_char ':' element in
  if List.length var_and_value = 1 then (mk_exp "None", Exp.Var "_")
  else
    let var = List.hd var_and_value |> String.trim in
    let value = List.tl var_and_value |> List.hd |> String.trim in
    (mk_exp var, mk_exp value)

let mk_field_list field =
  let field_list = String.split_on_char ',' field in
  List.map (fun x -> mk_field x) field_list

let prop_element x =
  let item = JsonUtil.to_string x in
  match item with
  | _ when String.starts_with ~prefix:"MEMne" item ->
      let procname_and_line =
        item |> Str.replace_first (Str.regexp "MEMne<") ""
      in
      let procname_and_line = String.split_on_char ':' procname_and_line in
      let procname = procname_and_line |> List.hd |> String.trim in
      let line_and_exp =
        procname_and_line |> List.tl |> List.hd |> String.split_on_char '>'
      in
      let line = line_and_exp |> List.hd |> int_of_string in
      let expression =
        line_and_exp |> List.tl |> List.hd
        |> Str.global_replace (Str.regexp "[()]") ""
        |> String.trim
      in
      let predsymb =
        PredSymb.MEM
          { PredSymb.kind = PredSymb.Mnew; pname = procname; location = line }
      in
      Predicate.Pred (predsymb, [ mk_exp expression ])
  | _ when String.starts_with ~prefix:"UND" item ->
      let list =
        item
        |> Str.replace_first (Str.regexp "UND<") ""
        |> String.split_on_char ':'
      in
      let procname =
        List.hd list |> Str.replace_first (Str.regexp ">") "" |> String.trim
      in
      let line_and_exp = List.tl list |> List.hd |> String.split_on_char '(' in
      let line = List.hd line_and_exp |> int_of_string in
      let expression =
        List.tl line_and_exp |> List.hd
        |> Str.replace_first (Str.regexp ")") ""
        |> String.trim
      in
      let predsymb = PredSymb.UND { pname = procname; location = line } in
      Predicate.Pred (predsymb, [ mk_exp expression ])
  | _ when String.starts_with ~prefix:"RET" item ->
      let list =
        item
        |> Str.replace_first (Str.regexp "RET<") ""
        |> String.split_on_char '>'
      in
      let procname = list |> List.hd |> String.trim in
      let var =
        list |> List.tl |> List.hd
        |> Str.global_replace (Str.regexp "[()]") ""
        |> String.trim
      in
      let predsymb = PredSymb.RET { pname = procname } in
      Predicate.Pred (predsymb, [ mk_exp var ])
  | _ when String.contains item '|' ->
      let list = String.split_on_char '|' item in
      let expression = List.hd list |> String.trim in
      let field_list =
        List.tl list |> List.hd
        |> Str.global_replace (Str.regexp "[->{}]") ""
        |> String.trim
      in
      let field = mk_field_list field_list in
      Predicate.Object (mk_exp expression, Exp.Field field)
  | _ when is_neq item ->
      let list = String.split_on_char '=' item in
      let variable =
        Exp.Var
          (List.hd list |> Str.replace_first (Str.regexp "!") "" |> String.trim)
      in
      let value = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Neq (variable, value)
  | _ when is_le item ->
      let item =
        item |> Str.global_replace (Str.regexp "[()=]") "" |> String.trim
      in
      let list = String.split_on_char '<' item in
      let left_var = List.hd list |> String.trim |> mk_exp in
      let right_var = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Le (left_var, right_var)
  | _ when is_ge item ->
      let item =
        item |> Str.global_replace (Str.regexp "[()=]") "" |> String.trim
      in
      let list = String.split_on_char '>' item in
      let left_var = List.hd list |> String.trim |> mk_exp in
      let right_var = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Ge (left_var, right_var)
  | _ when is_lt item ->
      let item =
        item |> Str.global_replace (Str.regexp "[()=]") "" |> String.trim
      in
      let list = String.split_on_char '<' item in
      let left_var = List.hd list |> String.trim |> mk_exp in
      let right_var = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Lt (left_var, right_var)
  | _ when is_gt item ->
      let item =
        item |> Str.global_replace (Str.regexp "[()=]") "" |> String.trim
      in
      let list = String.split_on_char '>' item in
      let left_var = List.hd list |> String.trim |> mk_exp in
      let right_var = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Gt (left_var, right_var)
  | _ when is_eq item ->
      let list = String.split_on_char '=' item in
      let variable = Exp.Var (List.hd list |> String.trim) in
      let value = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Eq (variable, value)
  | _ when String.equal item "" -> Predicate.None
  | _ ->
      "prop element " ^ item |> print_endline;
      failwith "prop element not implemented"

let name_split assoc method_map mmap =
  let method_name = JsonUtil.member "method" assoc |> JsonUtil.to_string in
  let method_name =
    if String.contains method_name ' ' then
      method_name |> String.split_on_char ' ' |> List.tl |> List.hd
    else method_name
  in
  let method_name = MethodMap.M.find method_name method_map in
  let summary =
    JsonUtil.member "prop" assoc
    |> JsonUtil.to_list
    |> List.map (fun x -> prop_element x)
  in
  let summary = if summary = [] then { prop = [] } else { prop = summary } in
  ErrorSummaryMap.M.add method_name summary mmap

(*mmap: one element *)
let replace_prop mmap =
  let candidate_prop =
    List.fold_left
      (fun list prop ->
        match prop with
        | Predicate.Eq (Var var, Symbol sym) -> (var, sym) :: list
        | _ -> list)
      [] mmap
  in
  let props =
    List.fold_left
      (fun modified_props prop ->
        match prop with
        | Predicate.Eq (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Eq (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Neq (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Neq (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Gt (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Gt (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Ge (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Ge (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Lt (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Lt (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Le (Symbol sym, value) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Le (Var can_var, value) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | Predicate.Object (Symbol sym, Field field) -> (
            let mk_prop =
              List.fold_left
                (fun prop candidate ->
                  let can_var, can_sym = candidate in
                  if sym = can_sym then
                    Predicate.Object (Var can_var, Field field) :: prop
                  else prop)
                [] candidate_prop
            in
            match mk_prop with
            | [] -> prop :: modified_props
            | hd :: _ -> hd :: modified_props)
        | _ -> prop :: modified_props)
      [] mmap
  in
  props

let from_json json target_method method_map =
  let error_summarys =
    List.fold_left
      (fun mmap item -> name_split item method_map mmap)
      ErrorSummaryMap.M.empty json
  in
  ErrorSummaryMap.M.fold
    (fun _ value init ->
      ErrorSummaryMap.M.add target_method
        { prop = replace_prop value.prop }
        init)
    error_summarys ErrorSummaryMap.M.empty
