module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module SummaryMap = Language.SummaryMap
module MethodInfo = Language.MethodInfo
module IG = Inheritance.G

let hashmap_put_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "key")
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "value")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let hashmap_put_premem =
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
       |> Condition.M.add (Condition.RH_Var "key") (Condition.RH_Symbol "v7")
       |> Condition.M.add (Condition.RH_Var "value") (Condition.RH_Symbol "v8")
       )

let hashmap_put_postmem =
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
       |> Condition.M.add (Condition.RH_Var "key") (Condition.RH_Symbol "v7")
       |> Condition.M.add (Condition.RH_Var "value") (Condition.RH_Symbol "v8")
       )
  |> Condition.M.add (Condition.RH_Symbol "v7")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v8")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)

let array_list_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let array_list_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let array_list_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let file_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "name")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let file_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "name") (Condition.RH_Symbol "v5"))

let file_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "name") (Condition.RH_Symbol "v5"))
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let file_create_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let file_create_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let file_create_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let image_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "w")
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "h")
  |> Condition.M.add (Condition.RH_Symbol "v4") (Condition.RH_Var "t")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let image_premem =
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
       |> Condition.M.add (Condition.RH_Var "w") (Condition.RH_Symbol "v9")
       |> Condition.M.add (Condition.RH_Var "h") (Condition.RH_Symbol "v10")
       |> Condition.M.add (Condition.RH_Var "t") (Condition.RH_Symbol "v11"))

let image_postmem =
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
       |> Condition.M.add (Condition.RH_Var "w") (Condition.RH_Symbol "v9")
       |> Condition.M.add (Condition.RH_Var "h") (Condition.RH_Symbol "v10")
       |> Condition.M.add (Condition.RH_Var "t") (Condition.RH_Symbol "v11"))
  |> Condition.M.add (Condition.RH_Symbol "v9")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v10")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v7") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v11")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v8") value_map)

let image_create_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let image_create_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let image_create_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let class_get_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let class_get_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let class_get_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let print_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "file")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let print_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "file") (Condition.RH_Symbol "v5"))

let print_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "file") (Condition.RH_Symbol "v5"))
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let file_input_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "file")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let file_input_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "file") (Condition.RH_Symbol "v5"))

let file_input_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "file") (Condition.RH_Symbol "v5"))
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let obj_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let obj_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let obj_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map)

let string_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "s")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let string_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "s") (Condition.RH_Symbol "v5"))

let string_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "s") (Condition.RH_Symbol "v5"))
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let array_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "size")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let array_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "size") (Condition.RH_Symbol "v5"))

let array_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v3") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (value_map
       |> Condition.M.add (Condition.RH_Var "size") (Condition.RH_Symbol "v5"))
  |> Condition.M.add (Condition.RH_Symbol "v5")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v4") value_map)

let hashmap_put_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (hashmap_put_var, hashmap_put_premem);
      postcond = (hashmap_put_var, hashmap_put_postmem);
      args = [];
    }

let array_list_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (array_list_var, array_list_premem);
      postcond = (array_list_var, array_list_postmem);
      args = [];
    }

let file_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (file_var, file_premem);
      postcond = (file_var, file_postmem);
      args = [];
    }

let file_create_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (file_create_var, file_create_premem);
      postcond = (file_create_var, file_create_postmem);
      args = [];
    }

let image_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (image_var, image_premem);
      postcond = (image_var, image_postmem);
      args = [];
    }

let image_create_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (image_create_var, image_create_premem);
      postcond = (image_create_var, image_create_postmem);
      args = [];
    }

let class_get_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (class_get_var, class_get_premem);
      postcond = (class_get_var, class_get_postmem);
      args = [];
    }

let print_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (print_var, print_premem);
      postcond = (print_var, print_postmem);
      args = [];
    }

let file_input_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (file_input_var, file_input_premem);
      postcond = (file_input_var, file_input_postmem);
      args = [];
    }

let obj_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (obj_var, obj_premem);
      postcond = (obj_var, obj_postmem);
      args = [];
    }

let string_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (string_var, string_premem);
      postcond = (string_var, string_postmem);
      args = [];
    }

let array_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (array_var, array_premem);
      postcond = (array_var, array_postmem);
      args = [];
    }

let hashmap_put_info =
  let this = ("java.util.HashMap", Language.This (Object "HashMap")) in
  let arg_typ = Language.Object "Object" in
  let arg1 = ("", Language.Var (arg_typ, "con_key")) in
  let arg2 = ("", Language.Var (arg_typ, "con_value")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg1; arg2 ];
      return = "void";
      filename = "";
    }

let array_list_info =
  let this = ("java.util.ArrayList", Language.This (Object "ArrayList")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let file_info =
  let this = ("java.io.File", Language.This (Object "File")) in
  let arg = ("", Language.Var (String, "unitcon_file")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let file_create_info =
  let this = ("java.io.File", Language.This (Object "File")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this ];
      return = "void";
      filename = "";
    }

let image_info =
  let this =
    ("java.awt.image.BufferedImage", Language.This (Object "BufferedImage"))
  in
  let arg1 = ("", Language.Var (Int, "con_width")) in
  let arg2 = ("", Language.Var (Int, "con_height")) in
  let arg3 = ("", Language.Var (Int, "con_type")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg1; arg2; arg3 ];
      return = "";
      filename = "";
    }

let image_create_info =
  let this =
    ("java.awt.image.BufferedImage", Language.This (Object "BufferedImage"))
  in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this ];
      return = "Graphics2D";
      filename = "";
    }

let class_get_info =
  let this = ("", Language.This (Object "Object")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this ];
      return = "Object";
      filename = "";
    }

let print_info =
  let this = ("java.io.PrintStream", Language.This (Object "PrintStream")) in
  let arg = ("java.io.File", Language.Var (Object "File", "con_file")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let file_input_info =
  let this =
    ("java.io.FileInputStream", Language.This (Object "FileInputStream"))
  in
  let arg = ("java.io.File", Language.Var (Object "File", "con_file")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let obj_info =
  let this = ("java.lang.Object", Language.This (Object "Object")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this ];
      return = "";
      filename = "";
    }

let string_info =
  let this = ("java.lang.String", Language.This (Object "String")) in
  let arg = ("java.lang.String", Language.Var (String, "con_string")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let int_array_info =
  let this = ("", Language.This (Array Int)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let long_array_info =
  let this = ("", Language.This (Array Long)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let float_array_info =
  let this = ("", Language.This (Array Float)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let double_array_info =
  let this = ("", Language.This (Array Double)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let bool_array_info =
  let this = ("", Language.This (Array Bool)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let char_array_info =
  let this = ("", Language.This (Array Char)) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let string_array_info =
  let this = ("", Language.This (Array (Object "String"))) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

let object_array_info =
  let this = ("", Language.This (Array (Object "Object"))) in
  let arg = ("", Language.Var (Int, "con_size")) in
  MethodInfo.
    {
      modifier = Language.Public;
      is_static = false;
      formal_params = [ this; arg ];
      return = "";
      filename = "";
    }

(*TODO: array_array_info *)

let add_java_package_summary mmap =
  SummaryMap.M.add "HashMap.put(Object,Object)" [ hashmap_put_summary ] mmap
  |> SummaryMap.M.add "ArrayList.<init>()" [ array_list_summary ]
  |> SummaryMap.M.add "File.<init>(String)" [ file_summary ]
  |> SummaryMap.M.add "File.createNewFile()" [ file_create_summary ]
  |> SummaryMap.M.add "BufferedImage.<init>(int,int,int)" [ image_summary ]
  |> SummaryMap.M.add "BufferedImage.createGraphics()" [ image_create_summary ]
  |> SummaryMap.M.add "Object.getClass()" [ class_get_summary ]
  |> SummaryMap.M.add "PrintStream.<init>(File)" [ print_summary ]
  |> SummaryMap.M.add "FileInputStream.<init>(File)" [ file_input_summary ]
  |> SummaryMap.M.add "Object.<init>()" [ obj_summary ]
  |> SummaryMap.M.add "String.<init>(String)" [ string_summary ]
  |> SummaryMap.M.add "IntArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "LongArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "FloatArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "DoubleArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "BoolArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "CharArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "StringArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "ObjectArray.<init>(int)" [ array_summary ]

let add_java_package_method mmap =
  MethodInfo.M.add "HashMap.put(Object,Object)" hashmap_put_info mmap
  |> MethodInfo.M.add "ArrayList.<init>()" array_list_info
  |> MethodInfo.M.add "File.<init>(String)" file_info
  |> MethodInfo.M.add "File.createNewFile()" file_create_info
  |> MethodInfo.M.add "BufferedImage.<init>(int,int,int)" image_info
  |> MethodInfo.M.add "BufferedImage.createGraphics()" image_create_info
  |> MethodInfo.M.add "Object.getClass()" class_get_info
  |> MethodInfo.M.add "PrintStream.<init>(File)" print_info
  |> MethodInfo.M.add "FileInputStream.<init>(File)" file_input_info
  |> MethodInfo.M.add "Object.<init>()" obj_info
  |> MethodInfo.M.add "String.<init>(String)" string_info
  |> MethodInfo.M.add "IntArray.<init>(int)" int_array_info
  |> MethodInfo.M.add "LongArray.<init>(int)" long_array_info
  |> MethodInfo.M.add "FloatArray.<init>(int)" float_array_info
  |> MethodInfo.M.add "DoubleArray.<init>(int)" double_array_info
  |> MethodInfo.M.add "BoolArray.<init>(int)" bool_array_info
  |> MethodInfo.M.add "CharArray.<init>(int)" char_array_info
  |> MethodInfo.M.add "StringArray.<init>(int)" string_array_info
  |> MethodInfo.M.add "ObjectArray.<init>(int)" object_array_info

let add_java_package_inheritance ig =
  let add_inheritance super child ig = IG.add_edge ig super child in
  add_inheritance "java.util.Collection" "java.util.ArrayList" ig
  |> add_inheritance "java.util.List" "java.util.ArrayList"
  |> add_inheritance "java.io.InputStream" "java.io.FileInputStream"
  |> add_inheritance "java.util.Map" "Java.util.HashMap"
