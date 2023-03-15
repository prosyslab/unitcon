module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module SummaryMap = Language.SummaryMap

let mk_hashmap_var =
  Condition.M.empty
  |> Condition.M.add (Condition.RH_Symbol "v2") (Condition.RH_Var "key")
  |> Condition.M.add (Condition.RH_Symbol "v3") (Condition.RH_Var "value")
  |> Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")

let mk_hashmap_premem =
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

let mk_hashmap_postmem =
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

let mk_hashmap_summary =
  Language.
    {
      relation = Relation.M.empty;
      value = Value.M.empty;
      precond = (mk_hashmap_var, mk_hashmap_premem);
      postcond = (mk_hashmap_var, mk_hashmap_postmem);
      args = [];
    }

let add_java_package_summary mmap =
  let hash_map = "HashMap.put(Object,Object)" in
  SummaryMap.M.add hash_map [ mk_hashmap_summary ] mmap
