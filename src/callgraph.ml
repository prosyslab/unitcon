type info = {
  method_name : string;
  modifier : string;
  param : string list;
}

module Node = struct
  include Map.Make (struct
    type t = info

    let compare = compare
  end)
end

module Callee = struct
  include Map.Make (struct
    type t = string

    let compare = compare
  end)
end

type t = {
  node : string list Node.t;
  edge : string list Callee.t;
}

let empty =
{
  node = Node.empty;
  edge = Callee.empty;
}