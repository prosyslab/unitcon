open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let value_maker is_err value = Value.{ from_error = is_err; value }

(* When parsing values between or outside, we need to normalize the value *)
let normalize_null is_max value =
  match int_of_string_opt value with
  | Some v -> Value.Int v
  | None ->
      if value = "null" then Value.Int 0
      else if is_max then Value.PlusInf
      else Value.MinusInf

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
    | "int" -> Int
    | "long" -> Long
    | "signed short" | "short" -> Short
    | "byte" | "signed char" -> Byte
    | "float" -> Float
    | "double" -> Double
    | "_Bool" | "boolean" -> Bool
    | "unsigned short" | "unsigned char" -> Char
    | "java.lang.String*" | "java.lang.String" -> String
    | "" -> NonType
    | _ when Str.string_match Regexp.array t 0 ->
        let typ = t |> Regexp.first_rm Regexp.rm_array |> get_type in
        Array typ
    | _ ->
        let typ = Regexp.global_rm (Str.regexp "\\*.*$") t in
        Object typ
  in
  if List.length v_and_t = 1 then Var (NonType, "")
  else
    let mk_variable var typ =
      if var = "this" then
        let typ = get_type typ in
        This typ
      else
        let typ = get_type typ in
        Var (typ, var)
    in
    let var = List.hd v_and_t in
    let typ = List.tl v_and_t |> List.hd in
    mk_variable var typ

let parse_boitv boitv =
  let check_relation head tail =
    match int_of_string_opt tail with
    | Some _ -> false
    | None -> if head = tail then false else true
  in
  let parse_relation rel mmap =
    let relation = Str.split Regexp.arrow rel in
    let head = List.hd relation |> Regexp.rm_space in
    let value_list = List.tl relation |> List.hd |> String.split_on_char ' ' in
    List.fold_left
      (fun mmap tail ->
        let tail =
          Regexp.first_rm Regexp.max tail
          |> Regexp.first_rm Regexp.min
          |> Regexp.global_rm Regexp.bk2
          |> Regexp.rm_space
        in
        if check_relation head tail then Relation.M.add head tail mmap else mmap)
      mmap value_list
  in
  let relation_list = Regexp.remove_bk boitv |> Str.split Regexp.bm in
  if relation_list = [] then Relation.M.empty
  else
    List.fold_left
      (fun mmap relation -> parse_relation relation mmap)
      Relation.M.empty relation_list

let parse_eq_value is_err sym value mmap =
  let v = Regexp.first_rm Regexp.eq value in
  match int_of_string_opt v with
  | Some v -> Value.M.add sym (Value.Eq (Int v) |> value_maker is_err) mmap
  | None ->
      if v = "null" then
        Value.M.add sym (Value.Eq Null |> value_maker is_err) mmap
      else Value.M.add sym (Value.Eq (String v) |> value_maker is_err) mmap

let parse_neq_value is_err sym value mmap =
  let v = Regexp.first_rm Regexp.neq value in
  match int_of_string_opt v with
  | Some v -> Value.M.add sym (Value.Neq (Int v) |> value_maker is_err) mmap
  | None ->
      if v = "null" then
        Value.M.add sym (Value.Neq Null |> value_maker is_err) mmap
      else Value.M.add sym (Value.Neq (String v) |> value_maker is_err) mmap

let parse_ge_value is_err sym value mmap =
  match Regexp.first_rm Regexp.ge value |> int_of_string_opt with
  | Some v -> Value.M.add sym (Value.Ge (Int v) |> value_maker is_err) mmap
  | None -> Value.M.add sym (Value.Ge MinusInf |> value_maker is_err) mmap

let parse_gt_value is_err sym value mmap =
  match Regexp.first_rm Regexp.gt value |> int_of_string_opt with
  | Some v -> Value.M.add sym (Value.Gt (Int v) |> value_maker is_err) mmap
  | None -> Value.M.add sym (Value.Gt MinusInf |> value_maker is_err) mmap

let parse_le_value is_err sym value mmap =
  match Regexp.first_rm Regexp.le value |> int_of_string_opt with
  | Some v -> Value.M.add sym (Value.Le (Int v) |> value_maker is_err) mmap
  | None -> Value.M.add sym (Value.Le PlusInf |> value_maker is_err) mmap

let parse_lt_value is_err sym value mmap =
  match Regexp.first_rm Regexp.lt value |> int_of_string_opt with
  | Some v -> Value.M.add sym (Value.Lt (Int v) |> value_maker is_err) mmap
  | None -> Value.M.add sym (Value.Lt PlusInf |> value_maker is_err) mmap

let parse_between_value is_err sym value mmap =
  let values =
    Regexp.first_rm Regexp.in_n value
    |> Regexp.first_rm Regexp.in_bk
    |> Regexp.first_rm Regexp.end_bk
    |> String.split_on_char ' '
  in
  if List.length values = 1 then
    Value.M.add sym
      (Value.Between (MinusInf, PlusInf) |> value_maker is_err)
      mmap
  else
    let min_value = List.hd values in
    let max_value = List.tl values |> List.hd in
    Value.M.add sym
      (Value.Between
         (normalize_null false min_value, normalize_null true max_value)
      |> value_maker is_err)
      mmap

let parse_outside_value is_err sym value mmap =
  let values =
    Regexp.first_rm Regexp.ots value
    |> Regexp.first_rm Regexp.end_bk
    |> String.split_on_char ' '
  in
  let min_value = List.hd values in
  let max_value = List.tl values |> List.hd in
  Value.M.add sym
    (Value.Outside
       (normalize_null false min_value, normalize_null true max_value)
    |> value_maker is_err)
    mmap

let parse_value is_err v mmap =
  let mapping_v = Str.split Regexp.arrow v in
  let hd = List.hd mapping_v |> Regexp.rm_space in
  let tl = List.tl mapping_v |> List.hd |> Regexp.rm_space in
  if Value.is_eq tl then parse_eq_value is_err hd tl mmap
  else if Value.is_neq tl then parse_neq_value is_err hd tl mmap
  else if Value.is_ge tl then parse_ge_value is_err hd tl mmap
  else if Value.is_gt tl then parse_gt_value is_err hd tl mmap
  else if Value.is_le tl then parse_le_value is_err hd tl mmap
  else if Value.is_lt tl then parse_lt_value is_err hd tl mmap
  else if Value.is_between tl then parse_between_value is_err hd tl mmap
  else if Value.is_outside tl then parse_outside_value is_err hd tl mmap
  else failwith "parse_citv error"

let parse_citv is_err mem citv =
  let value_list = Regexp.remove_bk citv |> Str.split Regexp.bm in
  let init_value =
    Condition.M.fold
      (fun head tail val_map ->
        if Condition.M.cardinal tail > 1 then
          Value.M.add (head |> AST.get_rh_name)
            (Value.Neq Null |> value_maker is_err)
            val_map
        else val_map)
      mem Value.M.empty
  in
  if value_list = [] then init_value
  else
    List.fold_left
      (fun mmap mapping_value -> parse_value is_err mapping_value mmap)
      init_value value_list

let parse_var var =
  if var = "[{ }]" then Condition.M.empty
  else
    let var_list =
      var
      |> Regexp.global_rm Regexp.open_bk
      |> Regexp.global_rm Regexp.end_bk
      |> Regexp.global_rm Regexp.remain_symbol
      |> String.split_on_char ','
    in
    List.fold_left
      (fun mmap var ->
        let i_and_s = String.split_on_char '=' var in
        let id = List.hd i_and_s |> Regexp.rm_space in
        if String.length id = 0 then mmap
        else if List.tl i_and_s = [] then mmap
        else
          let symbol = List.tl i_and_s |> List.hd |> Regexp.rm_space in
          Condition.M.add (symbol |> mk_rh_type) (Condition.RH_Var id) mmap)
      Condition.M.empty var_list

let rec mk_ref_map ref_trace mmap =
  match ref_trace with
  | hd :: tl -> (
      if hd |> Regexp.rm_space = "" then mmap
      else
        let ref = Str.split (Str.regexp "->") hd in
        try
          let field = List.hd ref |> Regexp.rm_space |> mk_rh_type in
          let value = List.tl ref |> List.hd |> Regexp.rm_space |> mk_rh_type in
          Condition.M.add field value mmap |> mk_ref_map tl
        with _ -> mk_ref_map tl mmap)
  | [] -> mmap

let parse_ref_mem ref mmap =
  let ref_trace =
    Regexp.global_rm Regexp.start_bm ref
    |> Regexp.rm_space |> Str.split Regexp.bm
  in
  if ref_trace = [] || Str.string_match Regexp.ref (List.hd ref_trace) 0 then
    mmap
  else
    let head =
      List.hd ref_trace |> Str.split Regexp.arrow |> List.hd |> Regexp.rm_space
    in
    let partial_tl =
      List.hd ref_trace
      |> Regexp.global_rm ("^" ^ head ^ "[ \t\r\n]+->" |> Str.regexp)
      |> Regexp.rm_space
    in
    let trace = List.tl ref_trace |> List.cons partial_tl in
    let trace = mk_ref_map trace Condition.M.empty in
    Condition.M.add (head |> mk_rh_type) trace mmap

let parse_mem mem =
  if mem = "[{ }]" then Condition.M.empty
  else
    let mem =
      mem
      |> Regexp.global_rm Regexp.remain_symbol2
      |> Regexp.first_rm Regexp.o_bks
      |> Regexp.first_rm Regexp.c_bks
      |> Regexp.global_rm Regexp.o_bk
      |> Regexp.rm_space |> Str.split Regexp.c_bk
    in
    List.fold_left
      (fun mmap ref -> parse_ref_mem ref mmap)
      Condition.M.empty mem

let parse_args args =
  let arg_list = Str.split Regexp.space args in
  List.fold_left
    (fun lst arg ->
      let a = Regexp.rm_space arg in
      if a = "" then lst else a :: lst)
    [] arg_list
  |> List.rev

let split_name m =
  if String.contains m ':' then m |> Str.split Regexp.colon |> List.hd else m

let split_return m =
  if String.contains m ':' then
    m |> Str.split Regexp.colon |> List.rev |> List.hd
  else ""
