open Language
module IG = Inheritance.G

(* ************************************** *
   Method Summary
 * ************************************** *)

(* # of formal parameters is 0 *)
let zero_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

(* # of formal parameters is 1
   p is parameter's name *)
let one_var p =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var p)
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

(* # of formal parameters is 2
   p1 is first parameter's name
   p2 is second parameter's name *)
let two_var p1 p2 =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var p2)
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var p1)
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

(* # of formal parameters is 3
   p1 is first parameter's name
   p2 is second parameter's name
   p3 is third parameter's name *)
let three_var p1 p2 p3 =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v4") (Condition.RH_Var p3)
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var p2)
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var p1)
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

(* when # of formal parameters is 0, post_mem is same to pre_mem *)
let zero_mem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let one_premem p =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var p) (Condition.RH_Symbol "v5"))

let one_postmem p =
  let value_map = Condition.M.empty in
  one_premem p
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let two_premem p1 p2 =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v4")
       (value_map
       |> Condition.M.add (Condition.RH_Var p1) (Condition.RH_Symbol "v7")
       |> Condition.M.add (Condition.RH_Var p2) (Condition.RH_Symbol "v8"))

let two_postmem p1 p2 =
  let value_map = Condition.M.empty in
  two_premem p1 p2
  |> Condition.M.add (Condition.RH_Symbol "v7")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v8")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)

let three_premem p1 p2 p3 =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v7") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v4")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v8") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (value_map
       |> Condition.M.add (Condition.RH_Var p1) (Condition.RH_Symbol "v9")
       |> Condition.M.add (Condition.RH_Var p2) (Condition.RH_Symbol "v10")
       |> Condition.M.add (Condition.RH_Var p3) (Condition.RH_Symbol "v11"))

let three_postmem p1 p2 p3 =
  let value_map = Condition.M.empty in
  three_premem p1 p2 p3
  |> Condition.M.add (Condition.RH_Symbol "v9")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v10")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v7") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v11")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v8") value_map)

let map_put_summary =
  let map_put_var = two_var "key" "value" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (map_put_var, two_premem "key" "value");
    postcond = (map_put_var, two_postmem "key" "value");
    args = [];
  }

let array_list_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let file_summary =
  let file_var = one_var "file" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (file_var, one_premem "file");
    postcond = (file_var, one_postmem "file");
    args = [];
  }

let image_summary =
  let image_var = three_var "w" "h" "t" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (image_var, three_premem "w" "h" "t");
    postcond = (image_var, three_postmem "w" "h" "t");
    args = [];
  }

let image_create_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let class_get_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let print_summary =
  let print_var = one_var "file" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (print_var, one_premem "file");
    postcond = (print_var, one_postmem "file");
    args = [];
  }

let file_input_summary =
  let file_input_var = one_var "file" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (file_input_var, one_premem "file");
    postcond = (file_input_var, one_postmem "file");
    args = [];
  }

let ba_output_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let obj_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let random_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let stringwriter_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (zero_var, zero_mem);
    postcond = (zero_var, zero_mem);
    args = [];
  }

let parseposition_summary =
  let parseposition_var = one_var "index" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (parseposition_var, one_premem "index");
    postcond = (parseposition_var, one_postmem "index");
    args = [];
  }

let bigdecimal_summary =
  let bigdecimal_var = one_var "val" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (bigdecimal_var, one_premem "val");
    postcond = (bigdecimal_var, one_postmem "val");
    args = [];
  }

let string_summary =
  let string_var = one_var "s" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (string_var, one_premem "s");
    postcond = (string_var, one_postmem "s");
    args = [];
  }

let array_summary =
  let array_var = one_var "size" in
  let array_value =
    Value.M.empty
    |> Value.M.add "v4" Value.{ from_error = false; value = Value.Ge (Int 1) }
  in
  {
    relation = Relation.M.empty;
    value = array_value;
    use_field = UseFieldMap.M.empty;
    precond = (array_var, one_premem "size");
    postcond = (array_var, one_postmem "size");
    args = [];
  }

let array_set_summary =
  let array_set_var = two_var "index" "elem" in
  let array_set_value =
    Value.M.empty
    |> Value.M.add "v5" Value.{ from_error = false; value = Value.Ge (Int 0) }
  in
  {
    relation = Relation.M.empty;
    value = array_set_value;
    use_field = UseFieldMap.M.empty;
    precond = (array_set_var, two_premem "index" "elem");
    postcond = (array_set_var, two_postmem "index" "elem");
    args = [];
  }

let point_summary =
  let point_var = two_var "x" "y" in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (point_var, two_premem "x" "y");
    postcond = (point_var, two_postmem "x" "y");
    args = [];
  }

(* ************************************** *
   Method Info
 * ************************************** *)

let map_put_info =
  let this = This (Object "java.util.Map") in
  let arg_typ = Object "java.lang.Object" in
  let arg1 = Var (arg_typ, "key") in
  let arg2 = Var (arg_typ, "value") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let array_list_info =
  let this = This (Object "java.util.ArrayList") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let file_info =
  let this = This (Object "java.io.File") in
  let arg = Var (String, "file") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let image_info =
  let this = This (Object "java.awt.image.BufferedImage") in
  let arg1 = Var (Int, "w") in
  let arg2 = Var (Int, "h") in
  let arg3 = Var (Int, "t") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2; arg3 ];
      return = "";
      filename = "";
    }

let image_create_info =
  let this = This (Object "java.awt.image.BufferedImage") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "Graphics2D";
      filename = "";
    }

let class_get_info =
  let this = This (Object "java.lang.Object") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "java.lang.Class";
      filename = "";
    }

let print_info =
  let this = This (Object "java.io.PrintStream") in
  let arg = Var (Object "java.io.File", "file") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let file_input_info =
  let this = This (Object "java.io.FileInputStream") in
  let arg = Var (Object "java.io.File", "file") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let ba_output_info =
  let this = This (Object "java.io.ByteArrayOutputStream") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let obj_info =
  let this = This (Object "java.lang.Object") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let random_info =
  let this = This (Object "java.util.Random") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let stringwriter_info =
  let this = This (Object "java.io.StringWriter") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let parseposition_info =
  let this = This (Object "java.text.ParsePosition") in
  let arg = Var (Int, "index") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let bigdecimal_info =
  let this = This (Object "java.math.BigDecimal") in
  let arg = Var (Int, "val") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let string_info =
  let this = This String in
  let arg = Var (String, "s") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let int_array_info =
  let this = This (Array Int) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let long_array_info =
  let this = This (Array Long) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let short_array_info =
  let this = This (Array Short) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let byte_array_info =
  let this = This (Array Byte) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let float_array_info =
  let this = This (Array Float) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let double_array_info =
  let this = This (Array Double) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let bool_array_info =
  let this = This (Array Bool) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let char_array_info =
  let this = This (Array Char) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let string_array_info =
  let this = This (Array String) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let object_array_info =
  let this = This (Array (Object "java.lang.Object")) in
  let arg = Var (Int, "size") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

(*TODO: array_array_info *)

let int_array_set_info =
  let this = This (Array Int) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Int, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let long_array_set_info =
  let this = This (Array Long) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Long, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let short_array_set_info =
  let this = This (Array Short) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Short, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let byte_array_set_info =
  let this = This (Array Char) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Byte, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let float_array_set_info =
  let this = This (Array Float) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Float, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let double_array_set_info =
  let this = This (Array Double) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Double, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let bool_array_set_info =
  let this = This (Array Bool) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Bool, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let char_array_set_info =
  let this = This (Array Char) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Char, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let string_array_set_info =
  let this = This (Array String) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (String, "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let object_array_set_info =
  let this = This (Array (Object "java.lang.Object")) in
  let arg1 = Var (Int, "index") in
  let arg2 = Var (Object "java.lang.Object", "elem") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let point_info =
  let this = This (Object "java.awt.Point") in
  let arg1 = Var (Int, "x") in
  let arg2 = Var (Int, "y") in
  MethodInfo.
    {
      modifier = Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "";
      filename = "";
    }

let add_java_package_summary mmap =
  SummaryMap.M.add "java.util.Map.put(java.lang.Object,java.lang.Object)"
    ([ map_put_summary ], []) mmap
  |> SummaryMap.M.add "java.util.ArrayList.<init>()" ([ array_list_summary ], [])
  |> SummaryMap.M.add "java.io.File.<init>(java.lang.String)"
       ([ file_summary ], [])
  |> SummaryMap.M.add "java.awt.image.BufferedImage.<init>(int,int,int)"
       ([ image_summary ], [])
  |> SummaryMap.M.add "java.awt.image.BufferedImage.createGraphics()"
       ([ image_create_summary ], [])
  |> SummaryMap.M.add "java.lang.Object.getClass()" ([ class_get_summary ], [])
  |> SummaryMap.M.add "java.io.PrintStream.<init>(java.io.File)"
       ([ print_summary ], [])
  |> SummaryMap.M.add "java.io.FileInputStream.<init>(java.io.File)"
       ([ file_input_summary ], [])
  |> SummaryMap.M.add "java.io.java.io.ByteArrayOutputStream.<init>()"
       ([ ba_output_summary ], [])
  |> SummaryMap.M.add "java.lang.Object.<init>()" ([ obj_summary ], [])
  |> SummaryMap.M.add "java.util.Random.<init>()" ([ random_summary ], [])
  |> SummaryMap.M.add "java.io.StringWriter.<init>()"
       ([ stringwriter_summary ], [])
  |> SummaryMap.M.add "java.text.ParsePosition.<init>(int)"
       ([ parseposition_summary ], [])
  |> SummaryMap.M.add "java.math.BigDecimal.<init>(int)"
       ([ bigdecimal_summary ], [])
  |> SummaryMap.M.add "java.lang.String.<init>(java.lang.String)"
       ([ string_summary ], [])
  |> SummaryMap.M.add "IntArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "LongArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "ShortArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "ByteArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "FloatArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "DoubleArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "BoolArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "CharArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "StringArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "ObjectArray.<init>(int)" ([ array_summary ], [])
  |> SummaryMap.M.add "IntArray.set(int,int)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "LongArray.set(int,long)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "ShortArray.set(int,short)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "ByteArray.set(int,byte)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "FloatArray.set(int,float)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "DoubleArray.set(int,double)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "BoolArray.set(int,boolean)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "CharArray.set(int,char)" ([ array_set_summary ], [])
  |> SummaryMap.M.add "StringArray.set(int,java.lang.String)"
       ([ array_set_summary ], [])
  |> SummaryMap.M.add "ObjectArray.set(int,java.lang.Object)"
       ([ array_set_summary ], [])
  |> SummaryMap.M.add "java.awt.Point.<init>(int,int)" ([ point_summary ], [])

let add_java_package_method mmap =
  MethodInfo.M.add "java.util.Map.put(java.lang.Object,java.lang.Object)"
    map_put_info mmap
  |> MethodInfo.M.add "java.util.ArrayList.<init>()" array_list_info
  |> MethodInfo.M.add "java.io.File.<init>(java.lang.String)" file_info
  |> MethodInfo.M.add "java.awt.image.BufferedImage.<init>(int,int,int)"
       image_info
  |> MethodInfo.M.add "java.awt.image.BufferedImage.createGraphics()"
       image_create_info
  |> MethodInfo.M.add "java.lang.Object.getClass()" class_get_info
  |> MethodInfo.M.add "java.io.PrintStream.<init>(java.io.File)" print_info
  |> MethodInfo.M.add "java.io.FileInputStream.<init>(java.io.File)"
       file_input_info
  |> MethodInfo.M.add "java.io.ByteArrayOutputStream.<init>()" ba_output_info
  |> MethodInfo.M.add "java.lang.Object.<init>()" obj_info
  |> MethodInfo.M.add "java.util.Random.<init>()" random_info
  |> MethodInfo.M.add "java.io.StringWriter.<init>()" stringwriter_info
  |> MethodInfo.M.add "java.text.ParsePosition.<init>(int)" parseposition_info
  |> MethodInfo.M.add "java.math.BigDecimal.<init>(int)" bigdecimal_info
  |> MethodInfo.M.add "java.lang.String.<init>(java.lang.String)" string_info
  |> MethodInfo.M.add "IntArray.<init>(int)" int_array_info
  |> MethodInfo.M.add "LongArray.<init>(int)" long_array_info
  |> MethodInfo.M.add "ShortArray.<init>(int)" short_array_info
  |> MethodInfo.M.add "ByteArray.<init>(int)" byte_array_info
  |> MethodInfo.M.add "FloatArray.<init>(int)" float_array_info
  |> MethodInfo.M.add "DoubleArray.<init>(int)" double_array_info
  |> MethodInfo.M.add "BoolArray.<init>(int)" bool_array_info
  |> MethodInfo.M.add "CharArray.<init>(int)" char_array_info
  |> MethodInfo.M.add "StringArray.<init>(int)" string_array_info
  |> MethodInfo.M.add "ObjectArray.<init>(int)" object_array_info
  |> MethodInfo.M.add "IntArray.set(int,int)" int_array_set_info
  |> MethodInfo.M.add "LongArray.set(int,long)" long_array_set_info
  |> MethodInfo.M.add "ShortArray.set(int,short)" short_array_set_info
  |> MethodInfo.M.add "ByteArray.set(int,byte)" byte_array_set_info
  |> MethodInfo.M.add "FloatArray.set(int,float)" float_array_set_info
  |> MethodInfo.M.add "DoubleArray.set(int,double)" double_array_set_info
  |> MethodInfo.M.add "BoolArray.set(int,boolean)" bool_array_set_info
  |> MethodInfo.M.add "CharArray.set(int,char)" char_array_set_info
  |> MethodInfo.M.add "StringArray.set(int,java.lang.String)"
       string_array_set_info
  |> MethodInfo.M.add "ObjectArray.set(int,java.lang.Object)"
       object_array_set_info
  |> MethodInfo.M.add "java.awt.Point.<init>(int,int)" point_info

let add_java_package_inheritance ig =
  let add_inheritance super child ig = IG.add_edge ig super child in
  add_inheritance "java.util.Collection" "java.util.ArrayList" ig
  |> add_inheritance "java.util.List" "java.util.ArrayList"
  |> add_inheritance "java.io.InputStream" "java.io.FileInputStream"
  |> add_inheritance "java.util.Map" "java.util.HashMap"
  |> add_inheritance "java.lang.Object" "java.lang.String"
  |> add_inheritance "java.lang.Object" "java.lang.Number"
  |> add_inheritance "java.lang.Number" "java.math.BigDecimal"
  |> add_inheritance "java.lang.CharSequence" "java.lang.String"
  |> add_inheritance "java.io.Writer" "java.io.StringWriter"
  |> add_inheritance "java.io.Serializable" "java.text.Format"
  |> add_inheritance "java.io.OutputStream" "java.io.ByteArrayOutputStream"
