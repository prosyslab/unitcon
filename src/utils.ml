module Condition = Language.Condition

let get_next_symbol symbol memory =
  match Condition.M.find_opt symbol memory with
  | Some sym -> (
      match Condition.M.find_opt Condition.RH_Any sym with
      | Some s -> s
      | None -> symbol)
  | None -> symbol