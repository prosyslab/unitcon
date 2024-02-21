open Language
module IG = Inheritance.G

(* ************************************** *
   Method Summary
 * ************************************** *)

let map_put_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "value")
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "key")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let map_put_premem =
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

let map_put_postmem =
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
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "file")
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
       |> Condition.M.add (Condition.RH_Var "file") (Condition.RH_Symbol "v5"))

let file_postmem =
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

(* let file_create_var =
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
          (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v2") value_map) *)

let image_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v4") (Condition.RH_Var "t")
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "h")
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "w")
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

let array_value =
  Value.M.empty
  |> Value.M.add "v4" Value.{ from_error = false; value = Value.Ge (Int 1) }

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

let array_set_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "elem")
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "index")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let array_set_value =
  Value.M.empty
  |> Value.M.add "v5" Value.{ from_error = false; value = Value.Ge (Int 0) }

let array_set_premem =
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
       |> Condition.M.add (Condition.RH_Var "index") (Condition.RH_Symbol "v7")
       |> Condition.M.add (Condition.RH_Var "elem") (Condition.RH_Symbol "v8"))

let array_set_postmem =
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
       |> Condition.M.add (Condition.RH_Var "index") (Condition.RH_Symbol "v7")
       |> Condition.M.add (Condition.RH_Var "elem") (Condition.RH_Symbol "v8"))
  |> Condition.M.add (Condition.RH_Symbol "v7")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v8")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)

let point_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "y")
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "x")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let point_premem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v7") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v4")
       (value_map
       |> Condition.M.add (Condition.RH_Var "x") (Condition.RH_Symbol "v8")
       |> Condition.M.add (Condition.RH_Var "y") (Condition.RH_Symbol "v9"))

let point_postmem =
  let value_map = Condition.M.empty in
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v1")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v5") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v2")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v6") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v3")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v7") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v4")
       (value_map
       |> Condition.M.add (Condition.RH_Var "x") (Condition.RH_Symbol "v8")
       |> Condition.M.add (Condition.RH_Var "y") (Condition.RH_Symbol "v9"))
  |> Condition.M.add (Condition.RH_Symbol "v6")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v8") value_map)
  |> Condition.M.add (Condition.RH_Symbol "v7")
       (Condition.M.add Condition.RH_Any (Condition.RH_Symbol "v9") value_map)

let map_put_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (map_put_var, map_put_premem);
    postcond = (map_put_var, map_put_postmem);
    args = [];
  }

let array_list_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (array_list_var, array_list_premem);
    postcond = (array_list_var, array_list_postmem);
    args = [];
  }

let file_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (file_var, file_premem);
    postcond = (file_var, file_postmem);
    args = [];
  }

let image_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (image_var, image_premem);
    postcond = (image_var, image_postmem);
    args = [];
  }

let image_create_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (image_create_var, image_create_premem);
    postcond = (image_create_var, image_create_postmem);
    args = [];
  }

let class_get_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (class_get_var, class_get_premem);
    postcond = (class_get_var, class_get_postmem);
    args = [];
  }

let print_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (print_var, print_premem);
    postcond = (print_var, print_postmem);
    args = [];
  }

let file_input_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (file_input_var, file_input_premem);
    postcond = (file_input_var, file_input_postmem);
    args = [];
  }

let obj_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (obj_var, obj_premem);
    postcond = (obj_var, obj_postmem);
    args = [];
  }

let string_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (string_var, string_premem);
    postcond = (string_var, string_postmem);
    args = [];
  }

let array_summary =
  {
    relation = Relation.M.empty;
    value = array_value;
    use_field = UseFieldMap.M.empty;
    precond = (array_var, array_premem);
    postcond = (array_var, array_postmem);
    args = [];
  }

let array_set_summary =
  {
    relation = Relation.M.empty;
    value = array_set_value;
    use_field = UseFieldMap.M.empty;
    precond = (array_set_var, array_set_premem);
    postcond = (array_set_var, array_set_postmem);
    args = [];
  }

let point_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (point_var, point_premem);
    postcond = (point_var, point_postmem);
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
    [ map_put_summary ] mmap
  |> SummaryMap.M.add "java.util.ArrayList.<init>()" [ array_list_summary ]
  |> SummaryMap.M.add "java.io.File.<init>(java.lang.String)" [ file_summary ]
  |> SummaryMap.M.add "java.awt.image.BufferedImage.<init>(int,int,int)"
       [ image_summary ]
  |> SummaryMap.M.add "java.awt.image.BufferedImage.createGraphics()"
       [ image_create_summary ]
  |> SummaryMap.M.add "java.lang.Object.getClass()" [ class_get_summary ]
  |> SummaryMap.M.add "java.io.PrintStream.<init>(java.io.File)"
       [ print_summary ]
  |> SummaryMap.M.add "java.io.FileInputStream.<init>(java.io.File)"
       [ file_input_summary ]
  |> SummaryMap.M.add "java.lang.Object.<init>()" [ obj_summary ]
  |> SummaryMap.M.add "java.lang.String.<init>(java.lang.String)"
       [ string_summary ]
  |> SummaryMap.M.add "IntArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "LongArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "ByteArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "FloatArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "DoubleArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "BoolArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "CharArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "StringArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "ObjectArray.<init>(int)" [ array_summary ]
  |> SummaryMap.M.add "IntArray.set(int,int)" [ array_set_summary ]
  |> SummaryMap.M.add "LongArray.set(int,long)" [ array_set_summary ]
  |> SummaryMap.M.add "ByteArray.set(int,byte)" [ array_set_summary ]
  |> SummaryMap.M.add "FloatArray.set(int,float)" [ array_set_summary ]
  |> SummaryMap.M.add "DoubleArray.set(int,double)" [ array_set_summary ]
  |> SummaryMap.M.add "BoolArray.set(int,boolean)" [ array_set_summary ]
  |> SummaryMap.M.add "CharArray.set(int,char)" [ array_set_summary ]
  |> SummaryMap.M.add "StringArray.set(int,java.lang.String)"
       [ array_set_summary ]
  |> SummaryMap.M.add "ObjectArray.set(int,java.lang.Object)"
       [ array_set_summary ]
  |> SummaryMap.M.add "java.awt.Point.<init>(int,int)" [ point_summary ]

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
  |> MethodInfo.M.add "java.lang.Object.<init>()" obj_info
  |> MethodInfo.M.add "java.lang.String.<init>(java.lang.String)" string_info
  |> MethodInfo.M.add "IntArray.<init>(int)" int_array_info
  |> MethodInfo.M.add "LongArray.<init>(int)" long_array_info
  |> MethodInfo.M.add "ByteArray.<init>(int)" byte_array_info
  |> MethodInfo.M.add "FloatArray.<init>(int)" float_array_info
  |> MethodInfo.M.add "DoubleArray.<init>(int)" double_array_info
  |> MethodInfo.M.add "BoolArray.<init>(int)" bool_array_info
  |> MethodInfo.M.add "CharArray.<init>(int)" char_array_info
  |> MethodInfo.M.add "StringArray.<init>(int)" string_array_info
  |> MethodInfo.M.add "ObjectArray.<init>(int)" object_array_info
  |> MethodInfo.M.add "IntArray.set(int,int)" int_array_set_info
  |> MethodInfo.M.add "LongArray.set(int,long)" long_array_set_info
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
