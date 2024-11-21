module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

(* compare *)
let compare_string = String.compare

let compare_bool = Bool.compare

let compare_list = List.compare

let compare_int = Int.compare

let compare_char = Char.compare

let compare_float = Float.compare

let compare_option cmp o1 o2 =
  match (o1, o2) with
  | Some x1, Some x2 -> cmp x1 x2
  | Some _, None -> 1
  | None, Some _ -> -1
  | None, None -> 0

(* equal *)
let equal_string = String.equal

let equal_bool = Bool.equal

let equal_list = List.equal

let equal_int = Int.equal

let equal_char = Char.equal

let equal_float = Float.equal

let equal_option eq o1 o2 =
  match (o1, o2) with
  | Some x1, Some x2 -> eq x1 x2
  | None, None -> true
  | _ -> false

type tc_completion = Complete | Need_Fuzzer | Need_Loop | Incomplete

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

let is_string = function String -> true | _ -> false

let is_primitive = function
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

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

module MethodInfo = struct
  module M = Map.Make (String)

  type info = {
    modifier : modifier;
    is_static : bool;
    formal_params : params;
    return : string;
    filename : file_name;
  }

  type t = info M.t
end

module ReturnType = struct
  module M = Map.Make (String)

  type t = method_name list M.t
end

module MethodType = struct
  module M = Map.Make (String)

  type t = method_name list M.t
end

module Relation = struct
  module M = Map.Make (String)

  type t = symbol M.t [@@deriving compare, equal]
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

  module M = Map.Make (String)

  type v = { from_error : bool; value : op } [@@deriving compare, equal]

  type t = v M.t [@@deriving compare, equal]

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
  [@@deriving compare, equal]

  module M = Map.Make (struct
    type t = rh [@@deriving compare, equal]
  end)

  type var = rh M.t (* symbol -> variable *) [@@deriving compare, equal]

  type mem = rh M.t M.t [@@deriving compare, equal]

  type t = var * mem [@@deriving compare, equal]
end

module Field = struct
  type t = { used_in_error : bool; name : string } [@@deriving compare, equal]
end

module FieldSet = Set.Make (Field)

module UseFieldMap = struct
  module M = Map.Make (struct
    type t = Condition.rh [@@deriving compare, equal]
  end)

  type t = FieldSet.t M.t [@@deriving compare, equal]
end

type summary = {
  relation : Relation.t;
  value : Value.t;
  use_field : UseFieldMap.t;
  precond : Condition.t;
  postcond : Condition.t;
  args : symbol list;
}
[@@deriving compare, equal]

let empty_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (Condition.M.empty, Condition.M.empty);
    postcond = (Condition.M.empty, Condition.M.empty);
    args = [];
  }

module SummaryMap = struct
  module M = Map.Make (String)

  (* list of summaries * list of fields with memory effects *)
  type t = (summary list * string list) M.t
end

module CallPropMap = struct
  module M = Map.Make (struct
    (* (caller * callee) *)
    type t = method_name * method_name [@@deriving compare, equal]
  end)

  type t = summary list M.t
end

module ClassInfo = struct
  module M = Map.Make (String)

  type info = { class_type : class_type }

  type t = info M.t
end

module SetterMap = struct
  module M = Map.Make (String)

  type setter = method_name * FieldSet.t

  type t = setter list M.t
end

module InstanceInfo = struct
  module M = Map.Make (String)

  type const = string

  (* enum name -> enum const list || class name -> pre-created instance list*)
  type t = const list M.t
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

let get_rh_name ?(is_var = false) rh =
  if is_var then match rh with Condition.RH_Var v -> v | _ -> ""
  else match rh with Condition.RH_Symbol s -> s | _ -> ""

let get_next_symbol symbol memory =
  match Condition.M.find_opt symbol memory with
  | Some sym -> (
      match Condition.M.find_opt Condition.RH_Any sym with
      | Some s -> s
      | None -> symbol)
  | None -> symbol

let get_id_symbol vars id =
  Condition.M.fold
    (fun symbol symbol_id find ->
      match symbol_id with
      | Condition.RH_Var v when v = id -> symbol
      | _ -> find)
    vars Condition.RH_Any

let rec get_tail_symbol field_name symbol memory =
  match Condition.M.find_opt symbol memory with
  | Some sym -> (
      match Condition.M.find_opt (Condition.RH_Var field_name) sym with
      | Some s -> get_tail_symbol field_name s memory
      | None -> (
          match Condition.M.find_opt Condition.RH_Any sym with
          | Some any_sym -> get_tail_symbol field_name any_sym memory
          | None -> symbol))
  | None -> symbol

let get_index_value (v : Value.v) : Field.t =
  match v.value with
  | Value.Eq (Int i) -> { used_in_error = v.from_error; name = string_of_int i }
  | Value.Ge (Int i) -> { used_in_error = v.from_error; name = string_of_int i }
  | Value.Gt (Int i) ->
      { used_in_error = v.from_error; name = string_of_int (i + 1) }
  | _ -> { used_in_error = false; name = "" }

let org_symbol id { precond = pre_var, pre_mem; _ } =
  let id_symbol = get_id_symbol pre_var id |> get_rh_name in
  Condition.M.fold
    (fun symbol symbol_trace find_variable ->
      let symbol = get_rh_name symbol in
      if symbol = id_symbol then
        Condition.M.fold
          (fun _ tail trace_find_var ->
            match tail with Condition.RH_Symbol s -> s | _ -> trace_find_var)
          symbol_trace find_variable
      else find_variable)
    pre_mem ""

let get_array_index array summary =
  let _, memory = summary.precond in
  let array_symbol = org_symbol array summary in
  let values = summary.value in
  let find_value s =
    Value.M.fold
      (fun symbol value find_value -> if symbol = s then value else find_value)
      values
      { from_error = false; value = Value.Eq NonValue }
  in
  match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
  | Some x ->
      Condition.M.fold
        (fun sym v ((idx, idx_value), (elem, elem_value)) ->
          match sym with
          | Condition.RH_Index s when idx = "" ->
              ( (s, find_value s),
                ( get_rh_name v,
                  find_value (get_tail_symbol "" v memory |> get_rh_name) ) )
          | _ -> ((idx, idx_value), (elem, elem_value)))
        x
        ( ("", { from_error = false; value = Value.Ge (Int 0) }),
          ("", { from_error = false; value = Value.Eq NonValue }) )
  | None ->
      ( ("", { from_error = false; value = Value.Ge (Int 0) }),
        ("", { from_error = false; value = Value.Eq NonValue }) )

let remove_array_index array idx summary =
  let _, memory = summary.precond in
  let array_symbol = org_symbol array summary in
  match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
  | Some x ->
      let array_new_mem =
        Condition.M.fold
          (fun sym _ new_mem ->
            match sym with
            | Condition.RH_Index i when idx = i ->
                Condition.M.remove sym new_mem
            | _ -> new_mem)
          x x
      in
      Condition.M.add (Condition.RH_Symbol array_symbol) array_new_mem memory
  | None -> memory

let array_field_var org_summary array =
  Condition.M.add
    (Condition.RH_Symbol (fst array |> fst))
    (Condition.RH_Var "index") (fst org_summary.precond)
  |> Condition.M.add
       (Condition.RH_Symbol (snd array |> fst))
       (Condition.RH_Var "elem")

let array_current_mem org_summary array =
  Condition.M.add (Condition.RH_Symbol "v5")
    (Condition.M.add (Condition.RH_Var "index")
       (Condition.RH_Symbol (fst array |> fst))
       Condition.M.empty)
    (snd org_summary.precond)
  |> Condition.M.add (Condition.RH_Var "elem")
       (Condition.M.add Condition.RH_Any
          (Condition.RH_Symbol (snd array |> fst))
          Condition.M.empty)

let next_summary_in_void org_summary new_mem =
  {
    relation = org_summary.relation;
    value = org_summary.value;
    use_field = org_summary.use_field;
    precond = (fst org_summary.precond, new_mem);
    postcond = (fst org_summary.postcond, new_mem);
    args = org_summary.args;
  }

let current_summary_in_assign org_summary new_var new_mem =
  {
    relation = org_summary.relation;
    value = org_summary.value;
    use_field = org_summary.use_field;
    precond = (new_var, new_mem);
    postcond = (new_var, new_mem);
    args = org_summary.args;
  }
