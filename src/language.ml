module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let compare_string = String.compare

let compare_list = List.compare

type method_name = string [@@deriving compare]

type class_name = string [@@deriving compare]

type file_name = string [@@deriving compare]

type modifier = Public | Private | Protected | Default [@@deriving compare]

type class_type =
  | Abstract
  | Static
  | Private
  | Abstract_and_Static
  | Normal
  | Interface
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
[@@deriving compare]

type id = string (*e.g. i *) [@@deriving compare]

type variable = This of typ | Var of typ * id [@@deriving compare]

type import = string (* package.class *) [@@deriving compare]

type params = (import * variable) list [@@deriving compare]

type symbol = string (*e.g. v1 *) [@@deriving compare]

let modifier_of_json json =
  JsonUtil.to_string json |> function
  | "Public" -> Public
  | "Private" -> Private
  | "Protected" -> Protected
  | "Default" -> Default
  | s -> failwith ("Unknown modifier " ^ s)

module MethodInfo = struct
  module M = Map.Make (struct
    type t = method_name [@@deriving compare]
  end)

  type info = {
    modifier : modifier;
    is_static : bool;
    formal_params : params;
    return : string;
    filename : file_name;
  }

  type t = info M.t
end

module Relation = struct
  module M = Map.Make (struct
    type t = symbol [@@deriving compare]
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
    type t = symbol [@@deriving compare]
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
  [@@deriving compare]

  module M = Map.Make (struct
    type t = rh [@@deriving compare]
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
    type t = method_name [@@deriving compare]
  end)

  type t = summary list M.t
end

module CallPropMap = struct
  module M = Map.Make (struct
    (* (caller * callee) *)
    type t = method_name * method_name [@@deriving compare]
  end)

  type t = summary list M.t
end

module ClassInfo = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type info = { class_type : class_type }

  type t = info M.t
end

module SetterMap = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type setter = method_name * id list

  type t = setter list M.t
end

module FieldMap = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type t = Value.op M.t
end
