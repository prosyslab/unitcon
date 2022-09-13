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

type t = { precond : precond; postcond : postcond; visited : visited }

type summary = t list

module SummaryMap = struct
  module M = Map.Make (struct
    (* type t = Method.t *)
    type t = string

    let compare = compare
  end)

  type t = summary M.t
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
  let item = Yojson.Safe.Util.to_string x in
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
  | _ -> failwith "not implemented"

let summary_split item =
  let v =
    Yojson.Safe.Util.member "visited" item
    |> Yojson.Safe.Util.to_list
    |> List.map (fun x -> Yojson.Safe.Util.to_string x |> int_of_string)
  in
  let pre =
    Yojson.Safe.Util.member "precond" item
    |> Yojson.Safe.Util.to_list
    |> List.map (fun x -> summary_element x)
  in
  let post =
    Yojson.Safe.Util.member "postcond" item
    |> Yojson.Safe.Util.to_list
    |> List.map (fun x -> summary_element x)
  in
  { precond = pre; postcond = post; visited = v }

let name_split assoc mmap =
  let name, summary_list = Yojson.Safe.Util.to_assoc assoc |> List.hd in
  let summary =
    Yojson.Safe.Util.to_list summary_list |> List.map (fun x -> summary_split x)
  in
  SummaryMap.M.add name summary mmap

let from_json json =
  List.fold_left (fun mmap item -> name_split item mmap) SummaryMap.M.empty json
