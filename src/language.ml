module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

type method_name = string

type class_name = string

type file_name = string

type modifier = Public | Private | Protected | Default [@@deriving compare]

type typ = Int | Float | String | Object of class_name | None

type id = string (*e.g. i *)

type variable = This of typ | Var of typ * id

type params = variable list

type symbol = string (*e.g. v1 *)

let modifier_of_json json =
  JsonUtil.to_string json |> function
  | "Public" -> Public
  | "Private" -> Private
  | "Protected" -> Protected
  | "Default" -> Default
  | s -> failwith ("Unknown modifier " ^ s)

let params_of_json json = List.map JsonUtil.to_string json

module MethodInfo = struct
  module M = Map.Make (struct
    type t = method_name

    let compare = compare
  end)

  type info = {
    modifier : modifier;
    formal_params : params;
    filename : file_name;
  }

  type t = info M.t
end

module Relation = struct
  module M = Map.Make (struct
    type t = symbol

    let compare = compare
  end)

  type t = symbol M.t
end

module Value = struct
  type value =
    | Int of int
    | Float of float
    | String of string
    | PlusInf
    | MinusInf
    | Null

  type t =
    | Eq of symbol * value
    | Neq of symbol * value
    | Le of symbol * value
    | Lt of symbol * value
    | Ge of symbol * value
    | Gt of symbol * value
    | Between of symbol * value * value
    | Outside of symbol * value * value

  let is_le str = String.contains str '<' && String.contains str '='

  let is_lt str = String.contains str '<' && String.contains str '=' |> not

  let is_ge str = String.contains str '>' && String.contains str '='

  let is_gt str = String.contains str '>' && String.contains str '=' |> not

  let is_neq str = String.contains str '!' && String.contains str '='

  let is_eq str =
    String.contains str '='
    && String.contains str '!' |> not
    && String.contains str '>' |> not
    && String.contains str '<' |> not

  let is_between str =
    String.contains str 'i' && String.contains str 'n'
    && String.contains str '['
    && String.contains str 't' |> not

  let is_outside str =
    String.contains str 'n' && String.contains str 'o'
    && String.contains str 't' && String.contains str '['
end

module Condition = struct
  module M = Map.Make (struct
    type t = symbol

    let compare = compare
  end)

  type rh = RH_Var of id | RH_Symbol of symbol

  type var = rh M.t

  type mem = rh list M.t

  type t = var * mem
end

type summary = {
  relation : Relation.t;
  value : Value.t list;
  precond : Condition.t;
  postcond : Condition.t;
}

module SummaryMap = struct
  module M = Map.Make (struct
    type t = method_name

    let compare = compare
  end)

  type t = summary list M.t
end
