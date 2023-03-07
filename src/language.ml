module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

type method_name = string

type class_name = string

type file_name = string

type modifier = Public | Private | Protected | Default [@@deriving compare]

type class_type = Abstract | Static | Abstract_and_Static | Normal | Interface
[@@deriving compare]

type typ =
  | Int
  | Long
  | Float
  | Double
  | Bool
  | Char
  | String
  | Object of class_name
  | Array of typ
  | None

type id = string (*e.g. i *)

type variable = This of typ | Var of typ * id

type import = string (* package.class *)

type params = (import * variable) list

type symbol = string (*e.g. v1 *)

let modifier_of_json json =
  JsonUtil.to_string json |> function
  | "Public" -> Public
  | "Private" -> Private
  | "Protected" -> Protected
  | "Default" -> Default
  | s -> failwith ("Unknown modifier " ^ s)

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
    | Long of int
    | Float of float
    | Double of float
    | Bool of bool
    | Char of char
    | String of string
    | PlusInf
    | MinusInf
    | Null

  type op =
    | Eq of value
    | Neq of value
    | Le of value
    | Lt of value
    | Ge of value
    | Gt of value
    | Between of value * value
    | Outside of value * value

  module M = Map.Make (struct
    type t = symbol

    let compare = compare
  end)

  type t = op M.t

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
    Str.string_match (Str.regexp "in_N") str 0
    || Str.string_match (Str.regexp "in\\[") str 0

  let is_outside str = Str.string_match (Str.regexp "not_in\\[") str 0
end

module Condition = struct
  type rh = RH_Var of id | RH_Symbol of symbol | RH_Index of symbol | RH_Any

  module M = Map.Make (struct
    type t = rh

    let compare = compare
  end)

  type var = rh M.t

  type mem = rh M.t M.t

  type t = var * mem
end

type summary = {
  relation : Relation.t;
  value : Value.t;
  precond : Condition.t;
  postcond : Condition.t;
  args : symbol list;
}

let empty_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    precond = (Condition.M.empty, Condition.M.empty);
    postcond = (Condition.M.empty, Condition.M.empty);
    args = [];
  }

module SummaryMap = struct
  module M = Map.Make (struct
    type t = method_name

    let compare = compare
  end)

  type t = summary list M.t
end

module CallPropMap = struct
  module M = Map.Make (struct
    (* (caller * callee) *)
    type t = method_name * method_name

    let compare = compare
  end)

  type t = summary list M.t
end

module ClassTypeInfo = struct
  module M = Map.Make (struct
    type t = class_name

    let compare = compare
  end)

  type t = class_type M.t
end

module SetterMap = struct
  module M = Map.Make (struct
    type t = class_name

    let compare = compare
  end)

  type setter = method_name * id list

  type t = setter list M.t
end

module FieldMap = struct
  module M = Map.Make (struct
    type t = string

    let compare = compare
  end)

  type t = Value.op M.t
end
