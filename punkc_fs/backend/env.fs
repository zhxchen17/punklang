module Env

module Hashtbl = FSharp.Compatibility.OCaml.Hashtbl

open Config

type env =
    { mut_set : Hashtbl.t<int, unit>
      named_refs : Hashtbl.t<int, Bir.bir_value> }

let empty_env() =
    { mut_set = Hashtbl.create table_size
      named_refs = Hashtbl.create table_size }

let new_func_name() =
    let (id, _) = Var.newvar None
    "f" + string id

let mangle_func_name id = "f" + string id
let mangle_name id = "v" + string id
