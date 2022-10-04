module Method = Language.Method
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

module Exp = struct
  (* todo: add array type *)
  type t =
    | Int of int
    | Float of float (* todo *)
    | String of string
    | Symbol of string
    | Var of Language.var
    | Field of (t * t) list
end

(* todo: move to language.ml/Method *)
module Procname = struct
  type class_name = { class_name : string; package : string option }

  type t = {
    method_name : string;
    parameters : Exp.t list;
    class_name : class_name;
  }
end

module PredSymb = struct
  type mem_kind = Mnew | Mnew_array

  (* pname: Method.t *)
  type mem = { kind : mem_kind; pname : string; location : int }

  type und = { pname : string; location : int }

  type t = MEM of mem | UND of und
end

module Predicate = struct
  type t =
    | Eq of Exp.t * Exp.t
    | Neq of Exp.t * Exp.t
    | Pred of PredSymb.t * Exp.t list
    | Npred of PredSymb.t * Exp.t list
    | Object of Exp.t * Exp.t
end

module Memory = struct
  type t = Predicate.t list
end

type precond = Memory.t

type postcond = Memory.t

type visited = int list

type filename = Filename of string

type typ = Typ of string

type param = typ * Exp.t

type t = {
  precond : precond;
  postcond : postcond;
  visited : visited;
  filename : filename;
  param : param list;
}

type summary = t list

type key = { filename : filename; visited : visited }

let rec visited_equal list1 list2 =
  match list1, list2 with
  | hd1::tl1, hd2::tl2 -> 
    if hd1 <> hd2 then 1 else visited_equal tl1 tl2
  | [], _::_ ->
    0
  | _::_, [] -> 
    0
  | [], [] ->
    0

let equal_key {filename=filename1; visited=visited1} {filename=filename2; visited=visited2} =
  match compare filename1 filename2 with
  | 0 -> visited_equal visited1 visited2
  | c -> c

module SummaryMap = struct
  module M = Map.Make (struct
    (* type t = Method.t *)
    type t = string

    let compare = compare
  end)

  type t = summary M.t
end

module FindMethodMap = struct
  module M = Map.Make (struct
    type t = key
    let rec list_compare list1 list2 =
      match list1, list2 with
      | hd1::tl1, hd2::tl2 -> 
        if hd1 <> hd2 then 1 else list_compare tl1 tl2
      | [], _::_ ->
        0
      | _::_, [] -> 
        0
      | [], [] ->
        0

    let compare_list = list_compare

    let compare {filename=filename1; visited=visited1} {filename=filename2; visited=visited2} =
      match compare filename1 filename2 with
      | 0 -> compare_list visited1 visited2
      | c -> c

  end)

  (* type t = Method.t M.t*)
  type t = string M.t
end

let mk_exp exp =
  let exp = Str.replace_first (Str.regexp ":") "" exp in
  match exp with
  | _ when String.contains exp '$' -> Exp.Symbol exp
  | _ -> ( try Exp.Int (int_of_string exp) with _ -> Exp.Var exp)

let mk_field element =
  let var_and_value = String.split_on_char ':' element in
  let var = List.hd var_and_value |> String.trim in
  let value = List.tl var_and_value |> List.hd |> String.trim in
  (mk_exp var, mk_exp value)

let mk_field_list field =
  let field_list = String.split_on_char ',' field in
  List.map (fun x -> mk_field x) field_list

let summary_element x =
  let item = JsonUtil.to_string x in
  match item with
  | _ when String.contains item '!' ->
      let list = String.split_on_char '=' item in
      let variable =
        Exp.Var
          (List.hd list |> Str.replace_first (Str.regexp "!") "" |> String.trim)
      in
      let value = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Neq (variable, value)
  | _ when String.contains item '=' ->
      let list = String.split_on_char '=' item in
      let variable = Exp.Var (List.hd list |> String.trim) in
      let value = List.tl list |> List.hd |> String.trim |> mk_exp in
      Predicate.Eq (variable, value)
  | _ when String.starts_with ~prefix:"MEMne" item ->
      let list = String.split_on_char '<' item |> List.tl |> List.hd in
      let list = String.split_on_char '>' list in
      let procname_and_line = List.hd list |> String.split_on_char ':' in
      let procname = List.hd procname_and_line |> String.trim in
      let line = List.tl procname_and_line |> List.hd |> int_of_string in
      let expression =
        List.tl list |> List.hd
        |> Str.global_replace (Str.regexp "[()]") ""
        |> String.trim
      in
      let predsymb =
        PredSymb.MEM
          { PredSymb.kind = PredSymb.Mnew; pname = procname; location = line }
      in
      Predicate.Pred (predsymb, [ mk_exp expression ])
  | _ when String.starts_with ~prefix:"UND" item ->
      let list = String.split_on_char '<' item |> List.tl |> List.hd in
      let list = String.split_on_char ':' list in
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
  | _ -> failwith "summary element not implemented"

let summary_split item filename param =
  let v =
    JsonUtil.member "visited" item
    |> JsonUtil.to_list
    |> List.map (fun x -> JsonUtil.to_string x |> int_of_string)
  in
  let pre =
    JsonUtil.member "precond" item
    |> JsonUtil.to_list
    |> List.map (fun x -> summary_element x)
  in
  let post =
    JsonUtil.member "postcond" item
    |> JsonUtil.to_list
    |> List.map (fun x -> summary_element x)
  in
  { precond = pre; postcond = post; visited = v; filename; param }

let param_split param =
  let var_and_typ = String.split_on_char ':' param in
  let var = var_and_typ |> List.hd in
  let typ = var_and_typ |> List.tl |> List.hd in
  let typ =
    if String.contains typ '*' then String.sub typ 0 (String.length typ - 1)
    else typ
  in
  (Typ typ, Exp.Var var)

let param_list list =
  List.map (fun x -> JsonUtil.to_string x |> param_split) list

let name_split assoc mmap =
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let method_name =
    if String.contains method_name ' ' then
      method_name |> String.split_on_char ' ' |> List.tl |> List.hd
    else method_name
  in
  let file_name =
    JsonUtil.member "filename" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let param = JsonUtil.member "param" assoc |> JsonUtil.to_list |> param_list in
  let summary =
    JsonUtil.member "summary" assoc
    |> JsonUtil.to_list
    |> List.map (fun x -> summary_split x (Filename file_name) param)
  in
  SummaryMap.M.add method_name summary mmap

let from_json json =
  List.fold_left (fun mmap item -> name_split item mmap) SummaryMap.M.empty json

let name_split_making_methodmap assoc mmap =
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let method_name =
    if String.contains method_name ' ' then
      method_name |> String.split_on_char ' ' |> List.tl |> List.hd
    else method_name
  in
  let file_name =
    JsonUtil.member "filename" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let visited_list item =
    JsonUtil.member "visited" item
    |> JsonUtil.to_list
    |> List.map (fun x -> JsonUtil.to_string x |> int_of_string)
  in
  let summary =
    JsonUtil.member "summary" assoc
    |> JsonUtil.to_list
    |> List.map (fun x -> visited_list x)
  in
  List.fold_left
    (fun mmap item ->
      FindMethodMap.M.add
        { filename = Filename file_name; visited = item }
        method_name mmap)
    mmap summary

let making_methodmap json =
  List.fold_left
    (fun mmap item -> name_split_making_methodmap item mmap)
    FindMethodMap.M.empty json
