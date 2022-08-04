type var = String of string

type args = var list


type exp = Command of string * args
         | String of string
         | Int of int
         | New of string * args

type t = Assignment of var * exp
       | Statement of var * exp
       | Sequence of t * t


