module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module MethodInfo = Language.MethodInfo

module Node = struct
  include String

  let hash = Hashtbl.hash
end

module ExtraCalleeSet = Set.Make (struct
  let compare_string = String.compare

  type t = string [@@deriving compare]
end)

module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional (Node)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []
end

let get_caller_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_name
  in
  method_name

let get_callee_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "callee" assoc
    |> JsonUtil.to_list
    |> List.fold_left (fun l m -> (JsonUtil.to_string m |> split_name) :: l) []
    |> List.rev
  in
  method_name

let get_extra_callee_method_name minfo assoc =
  let check param =
    match param with _, Language.This _ -> true | _ -> false
  in
  let rec check_this params =
    match params with
    | hd :: tl -> if check hd then true else check_this tl
    | _ -> false
  in
  let find_method_name name arg_cnt minfo =
    MethodInfo.M.fold
      (fun m_name m_info m_set ->
        if Str.string_match (".*\\." ^ name ^ "(" |> Str.regexp) m_name 0 then
          let cnt = m_info.MethodInfo.formal_params |> List.length in
          let cnt =
            if check_this m_info.MethodInfo.formal_params then cnt - 1 else cnt
          in
          if arg_cnt = cnt then ExtraCalleeSet.add m_name m_set else m_set
        else m_set)
      minfo ExtraCalleeSet.empty
  in
  JsonUtil.member "callee" assoc
  |> JsonUtil.to_list
  |> List.fold_left
       (fun set a ->
         let name = JsonUtil.member "callee" a |> JsonUtil.to_string in
         let arg = JsonUtil.member "num_of_arg" a |> JsonUtil.to_int in
         find_method_name name arg minfo |> ExtraCalleeSet.union set)
       ExtraCalleeSet.empty

let of_json json =
  JsonUtil.to_list json
  |> List.fold_left
       (fun g element ->
         let caller = get_caller_method_name element in
         get_callee_method_name element
         |> List.fold_left (fun g callee -> G.add_edge g callee caller) g)
       G.empty

let of_extra_json method_info callgraph json =
  JsonUtil.to_list json
  |> List.fold_left
       (fun g element ->
         let caller = JsonUtil.member "caller" element |> JsonUtil.to_string in
         match MethodInfo.M.find_opt caller method_info with
         | Some _ ->
             ExtraCalleeSet.fold
               (fun callee g -> G.add_edge g callee caller)
               (get_extra_callee_method_name method_info element)
               g
         | _ -> g)
       callgraph

module Graphviz = Graph.Graphviz.Dot (G)
include G
