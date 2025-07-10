include Ppx_compare_lib.Builtin
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

type tc_completion = Complete | Need_Loop | Incomplete

type cost = Inf | Int of int

type method_name = string [@@deriving compare, equal]

type class_name = string [@@deriving compare, equal]

type file_name = string [@@deriving compare, equal]

type modifier = Public | Private | Protected | Default
[@@deriving compare, equal]

(* class_type is only allowed to be public or default *)
type class_type =
  | Public
  | Private
  | Default (* including protected *)
  | Public_Static
  | Public_Abstract
  | Public_Static_Abstract
  | Private_Static
  | Private_Abstract
  | Private_Static_Abstract
  | Default_Static
  | Default_Abstract
  | Default_Static_Abstract
  | Public_Interface
  | Default_Interface
[@@deriving compare, equal]

type typ =
  | Int
  | Long
  | Short
  | Byte
  | Float
  | Double
  | Bool
  | Char
  | String
  | Object of class_name
  | Array of typ
  | NonType
[@@deriving compare, equal]

type id = string (* e.g. i *) [@@deriving compare, equal]

type variable = This of typ | Var of typ * id [@@deriving compare, equal]

type import = string (* package.class *) [@@deriving compare, equal]

type params = variable list [@@deriving compare, equal]

type symbol = string (* e.g. v1 *) [@@deriving compare, equal]

type method_info = {
  modifier : modifier;
  is_static : bool;
  formal_params : params;
  return : string;
  filename : file_name;
}

type class_info = { class_type : class_type }

let compare_cost (c1 : cost) (c2 : cost) =
  match (c1, c2) with
  | Int i1, Int i2 -> compare i1 i2
  | Int _, Inf -> -1
  | Inf, Int _ -> 1
  | Inf, Inf -> -1

let equal_cost c1 c2 = c1 = c2

let is_string = function String -> true | _ -> false

let is_primitive = function
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

let is_special_primitive = function
  | Object "java.lang.Integer"
  | Object "java.lang.Long"
  | Object "java.lang.Short"
  | Object "java.lang.Byte"
  | Object "java.lang.Float"
  | Object "java.lang.Double"
  | Object "java.lang.CharSequence" ->
      true
  | _ -> false

let convert_special_primitive_type = function
  | Object "java.lang.Integer" -> Int
  | Object "java.lang.Long" -> Long
  | Object "java.lang.Short" -> Short
  | Object "java.lang.Byte" -> Byte
  | Object "java.lang.Float" -> Float
  | Object "java.lang.Double" -> Double
  | Object "java.lang.CharSequence" -> String
  | t -> t

let rec get_array_typ typ =
  match typ with Array t -> get_array_typ t | _ -> typ

let rec get_array_dim typ =
  match typ with Array t -> get_array_dim t + 1 | _ -> 1

let get_array_class_name = function
  | Array typ -> (
      match get_array_typ typ with
      | Int -> "IntArray" ^ (get_array_dim typ |> string_of_int)
      | Long -> "LongArray" ^ (get_array_dim typ |> string_of_int)
      | Short -> "ShortArray" ^ (get_array_dim typ |> string_of_int)
      | Byte -> "ByteArray" ^ (get_array_dim typ |> string_of_int)
      | Float -> "FloatArray" ^ (get_array_dim typ |> string_of_int)
      | Double -> "DoubleArray" ^ (get_array_dim typ |> string_of_int)
      | Bool -> "BoolArray" ^ (get_array_dim typ |> string_of_int)
      | Char -> "CharArray" ^ (get_array_dim typ |> string_of_int)
      | String -> "StringArray" ^ (get_array_dim typ |> string_of_int)
      | Object class_name ->
          "Object" ^ class_name ^ "Array" ^ (get_array_dim typ |> string_of_int)
      | _ -> "")
  | _ -> ""

let get_class_name = function
  | Object n -> n
  | Array typ -> (
      match get_array_typ typ with
      | Int -> "IntArray"
      | Long -> "LongArray"
      | Short -> "ShortArray"
      | Byte -> "ByteArray"
      | Float -> "FloatArray"
      | Double -> "DoubleArray"
      | Bool -> "BoolArray"
      | Char -> "CharArray"
      | String -> "StringArray"
      | Object _ -> "ObjectArray"
      | _ -> "")
  | NonType -> ""
  | _ -> failwith "get_class_name: not supported"

let get_consume_func t =
  (match t with
  | Int -> "Int()"
  | Long -> "Long()"
  | Short -> "Short()"
  | Byte -> "Byte()"
  | Float -> "Float()"
  | Double -> "Double()"
  | Bool -> "Boolean()"
  | Char -> "Char()"
  | String -> "RemainingAsString()"
  | _ -> failwith "get_consume_func: not supported")
  |> String.cat "data.consume"

let modifier_of_json json : modifier =
  JsonUtil.to_string json |> function
  | "Protected" -> Protected
  | "Public" -> Public
  | "Private" -> Private
  | "Default" -> Default
  | s -> failwith ("Unknown modifier " ^ s)

module MethodInfoMap = struct
  module M = Map.Make (String)

  type t = method_info M.t

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let mem = M.mem

  let find = M.find

  let find_opt = M.find_opt

  let iter = M.iter

  let fold = M.fold

  let merge = M.merge
end

module StrToStrMap = struct
  module M = Map.Make (String)

  type t = string M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let mem = M.mem

  let find = M.find

  let find_opt = M.find_opt

  let iter = M.iter

  let fold = M.fold

  let merge = M.merge
end

module StrToStrsMap = struct
  module M = Map.Make (String)

  type t = string list M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let mem = M.mem

  let find = M.find

  let find_opt = M.find_opt

  let iter = M.iter

  let fold = M.fold

  let merge = M.merge
end

module ReturnTypeMap = struct
  (* type -> methods list *)
  include StrToStrsMap
end

module MethodTypeMap = struct
  (* type -> methods list *)
  include StrToStrsMap
end

module RelationMap = struct
  (* symbol -> symbol *)
  include StrToStrMap
end

module Value = struct
  type const =
    | Int of int
    | Long of int
    | Short of int
    | Byte of int
    | Float of float
    | Double of float
    | Bool of bool
    | Char of char
    | String of string
    | PlusInf
    | MinusInf
    | Null
    | NonValue (* Determining whether to use the default const *)
  [@@deriving compare, equal]

  type op =
    | Eq of const
    | Neq of const
    | Le of const
    | Lt of const
    | Ge of const
    | Gt of const
    | Between of const * const
    | Outside of const * const
  [@@deriving compare, equal]

  type t = { from_error : bool; value : op } [@@deriving compare, equal]

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
    Str.string_match Regexp.in_n str 0 || Str.string_match Regexp.in_bk str 0

  let is_outside str = Str.string_match (Str.regexp "not_in\\[") str 0

  let string_of_const = function
    | Int i -> "int " ^ string_of_int i
    | Long i -> "long " ^ string_of_int i
    | Short i -> "short " ^ string_of_int i
    | Byte i -> "byte " ^ string_of_int i
    | Float f -> "float " ^ string_of_float f
    | Double f -> "double " ^ string_of_float f
    | Bool b -> "bool " ^ string_of_bool b
    | Char c -> "char " ^ String.make 1 c
    | String s -> "string " ^ s
    | PlusInf -> "plus inf"
    | MinusInf -> "minus inf"
    | Null -> "null"
    | NonValue -> "non-value"

  let string_of_op = function
    | Eq c -> "Eq (" ^ string_of_const c ^ ")"
    | Neq c -> "Neq (" ^ string_of_const c ^ ")"
    | Le c -> "Le (" ^ string_of_const c ^ ")"
    | Lt c -> "Lt (" ^ string_of_const c ^ ")"
    | Ge c -> "Ge (" ^ string_of_const c ^ ")"
    | Gt c -> "Gt (" ^ string_of_const c ^ ")"
    | Between (c1, c2) ->
        "Between [(" ^ string_of_const c1 ^ "), (" ^ string_of_const c2 ^ ")]"
    | Outside (c1, c2) ->
        "Outside [(" ^ string_of_const c1 ^ "), (" ^ string_of_const c2 ^ ")]"

  let string_of v =
    "from_error: "
    ^ string_of_bool v.from_error
    ^ ", value: " ^ string_of_op v.value
end

module ValueMap = struct
  module M = Map.Make (String)

  type t = Value.t M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let iter = M.iter

  let merge = M.merge

  let string_of map =
    M.fold
      (fun sym v acc -> acc ^ "\n" ^ sym ^ " -> " ^ Value.string_of v)
      map ""
end

module Ident = struct
  type t = Var of id | Symbol of symbol | Index of symbol | Any
  [@@deriving compare, equal]

  let string_of = function
    | Var id -> "Var (" ^ id ^ ")"
    | Symbol sym -> "Symbol (" ^ sym ^ ")"
    | Index idx -> "Index [" ^ idx ^ "]"
    | Any -> "Any *"

  let string_of_var = function Var id -> id | _ -> ""

  let string_of_symbol = function Symbol sym -> sym | _ -> ""
end

module VariableMap = struct
  module M = Map.Make (Ident)

  (* symbol name -> variable name *)
  type t = Ident.t M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let mem = M.mem

  let find = M.find

  let find_opt = M.find_opt

  let iter = M.iter

  let fold = M.fold

  let merge = M.merge

  let string_of map =
    M.fold
      (fun var value acc ->
        acc ^ "\n" ^ Ident.string_of var ^ " -> " ^ Ident.string_of value)
      map ""
end

module Memory = struct
  module M = Map.Make (Ident)

  type t = Ident.t M.t M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let remove = M.remove

  let is_empty = M.is_empty

  let mem = M.mem

  let exists = M.exists

  let find = M.find

  let find_opt = M.find_opt

  let iter = M.iter

  let fold = M.fold

  let merge = M.merge

  let cardinal = M.cardinal

  let filter = M.filter

  let string_of_outer var = "outer var: " ^ Ident.string_of var ^ "!"

  let string_of_inner mem =
    M.fold
      (fun var value acc ->
        acc ^ "  " ^ Ident.string_of var ^ "->" ^ Ident.string_of value ^ "\n")
      mem ""

  let string_of mem =
    M.fold
      (fun var inner_mem acc ->
        acc ^ "\n" ^ string_of_outer var ^ "\n" ^ string_of_inner inner_mem)
      mem ""
end

module State = struct
  type t = VariableMap.t * Memory.t [@@deriving compare, equal]
end

module Field = struct
  type t = { used_in_error : bool; name : string } [@@deriving compare, equal]
end

module FieldSet = Set.Make (Field)
module RequiredMethodSet = Set.Make (String)

module UseFieldMap = struct
  module M = Map.Make (struct
    type t = Ident.t [@@deriving compare, equal]
  end)

  type t = FieldSet.t M.t [@@deriving compare, equal]

  let empty = M.empty

  let add = M.add

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let merge = M.merge
end

type summary = {
  cost : cost;
  relation : RelationMap.t;
  value : ValueMap.t;
  use_field : UseFieldMap.t;
  precond : State.t;
  postcond : State.t;
  args : symbol list;
}
[@@deriving compare, equal]

let empty_summary =
  {
    cost = Inf;
    relation = RelationMap.empty;
    value = ValueMap.empty;
    use_field = UseFieldMap.empty;
    precond = (VariableMap.empty, Memory.empty);
    postcond = (VariableMap.empty, Memory.empty);
    args = [];
  }

module SummaryMap = struct
  module M = Map.Make (String)

  (* list of summaries * list of fields with memory effects *)
  type t = (summary list * string list) M.t

  let empty = M.empty

  let add = M.add

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let merge = M.merge
end

module CallPropMap = struct
  module M = Map.Make (struct
    (* (caller * callee) *)
    type t = method_name * method_name [@@deriving compare, equal]
  end)

  type t = summary list M.t

  let empty = M.empty

  let add = M.add

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let iter = M.iter

  let merge = M.merge
end

module ClassInfoMap = struct
  module M = Map.Make (String)

  type t = class_info M.t

  let empty = M.empty

  let add = M.add

  let mem = M.mem

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let merge = M.merge
end

module SetterMap = struct
  module M = Map.Make (String)

  type setter = method_name * FieldSet.t

  type t = setter list M.t

  let empty = M.empty

  let add = M.add

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let merge = M.merge
end

module InstanceInfoMap = struct
  module M = Map.Make (String)

  type const = string

  (* enum name -> enum const list || class name -> pre-created instance list*)
  type t = const list M.t

  let empty = M.empty

  let add = M.add

  let find = M.find

  let find_opt = M.find_opt

  let fold = M.fold

  let merge = M.merge
end

module PrimitiveInfo = struct
  module TypeMap = Map.Make (struct
    type t = typ [@@deriving compare, equal]
  end)

  (* default class name: "" *)
  module ClassMap = Map.Make (String)

  type const = string

  (* type -> class name -> const list*)
  type t = const list ClassMap.t TypeMap.t
end

let get_next_symbol symbol memory =
  match Memory.find_opt symbol memory with
  | Some sym -> (
      match Memory.find_opt Ident.Any sym with Some s -> s | None -> symbol)
  | None -> symbol

let get_id_symbol vars id =
  VariableMap.fold
    (fun symbol symbol_id find ->
      match symbol_id with Ident.Var v when v = id -> symbol | _ -> find)
    vars Ident.Any

let rec get_tail_symbol field_name symbol memory =
  match Memory.find_opt symbol memory with
  | Some sym -> (
      match Memory.find_opt (Ident.Var field_name) sym with
      | Some s -> get_tail_symbol field_name s memory
      | None -> (
          match Memory.find_opt Ident.Any sym with
          | Some any_sym -> get_tail_symbol field_name any_sym memory
          | None -> symbol))
  | None -> symbol

let get_index_value (v : Value.t) : Field.t =
  match v.value with
  | Value.Eq (Int i) -> { used_in_error = v.from_error; name = string_of_int i }
  | Value.Ge (Int i) -> { used_in_error = v.from_error; name = string_of_int i }
  | Value.Gt (Int i) ->
      { used_in_error = v.from_error; name = string_of_int (i + 1) }
  | _ -> { used_in_error = false; name = "" }

let org_symbol id (pre_var, pre_mem) =
  let id_symbol = get_id_symbol pre_var id |> Ident.string_of_symbol in
  Memory.fold
    (fun symbol symbol_trace find_variable ->
      let symbol = Ident.string_of_symbol symbol in
      if symbol = id_symbol then
        Memory.fold
          (fun _ tail trace_find_var ->
            match tail with Ident.Symbol s -> s | _ -> trace_find_var)
          symbol_trace find_variable
      else find_variable)
    pre_mem ""

let get_array_index array { precond = pre_var, pre_mem; value; _ } =
  let array_symbol = org_symbol array (pre_var, pre_mem) in
  let find_value s =
    ValueMap.fold
      (fun symbol value find_value -> if symbol = s then value else find_value)
      value
      { from_error = false; value = Value.Eq NonValue }
  in
  match Memory.find_opt (Ident.Symbol array_symbol) pre_mem with
  | Some x ->
      Memory.fold
        (fun sym v ((idx, idx_value), (elem, elem_value)) ->
          match sym with
          | Ident.Index s when idx = "" ->
              ( (s, find_value s),
                ( Ident.string_of_symbol v,
                  find_value
                    (get_tail_symbol "" v pre_mem |> Ident.string_of_symbol) )
              )
          | _ -> ((idx, idx_value), (elem, elem_value)))
        x
        ( ("", { from_error = false; value = Value.Ge (Int 0) }),
          ("", { from_error = false; value = Value.Eq NonValue }) )
  | None ->
      ( ("", { from_error = false; value = Value.Ge (Int 0) }),
        ("", { from_error = false; value = Value.Eq NonValue }) )

let remove_array_index array idx { precond = pre_var, pre_mem; _ } =
  let array_symbol = org_symbol array (pre_var, pre_mem) in
  match Memory.find_opt (Ident.Symbol array_symbol) pre_mem with
  | Some x ->
      let array_new_mem =
        Memory.fold
          (fun sym _ new_mem ->
            match sym with
            | Ident.Index i when idx = i -> Memory.remove sym new_mem
            | _ -> new_mem)
          x x
      in
      Memory.add (Ident.Symbol array_symbol) array_new_mem pre_mem
  | None -> pre_mem

let array_field_var org_summary array =
  Memory.add
    (Ident.Symbol (fst array |> fst))
    (Ident.Var "index") (fst org_summary.precond)
  |> Memory.add (Ident.Symbol (snd array |> fst)) (Ident.Var "elem")

let array_current_mem org_summary array =
  Memory.add (Ident.Symbol "v5")
    (Memory.add (Ident.Var "index")
       (Ident.Symbol (fst array |> fst))
       Memory.empty)
    (snd org_summary.precond)
  |> Memory.add (Ident.Var "elem")
       (Memory.add Ident.Any (Ident.Symbol (snd array |> fst)) Memory.empty)

let next_summary_in_void org_summary new_mem =
  {
    cost = org_summary.cost;
    relation = org_summary.relation;
    value = org_summary.value;
    use_field = org_summary.use_field;
    precond = (fst org_summary.precond, new_mem);
    postcond = (fst org_summary.postcond, new_mem);
    args = org_summary.args;
  }

let current_summary_in_assign org_summary new_var new_mem =
  {
    cost = org_summary.cost;
    relation = org_summary.relation;
    value = org_summary.value;
    use_field = org_summary.use_field;
    precond = (new_var, new_mem);
    postcond = (new_var, new_mem);
    args = org_summary.args;
  }
