open OUnit2
open UnitconLib
open Language

let template = "template" >:: fun _ -> assert_equal ~msg:"template" 5 (2 + 3)

let lteq =
  "Less than or Equal" >:: fun _ ->
  assert_equal ~msg:"less than or equal" (Some Generator.TRUE)
    (Generator.check_eq_l_one ~is_le:true (Value.Int 0) (Value.Int 10))

let lt =
  "Less than" >:: fun _ ->
  assert_equal ~msg:"less than" (Some Generator.FALSE)
    (Generator.check_eq_l_one ~is_le:false (Value.Int 0) (Value.Int 0))

let suite = "suite" >::: [ lteq; lt ]

let _ = run_test_tt_main suite
