open OUnit2

let template = "template" >:: fun _ -> assert_equal ~msg:"template" 5 (2 + 3)

let suite = "suite" >::: [ template ]

let _ = OUnit2.run_test_tt_main suite
