module Env

module Hashtbl = FSharp.Compatibility.OCaml.Hashtbl

open Config

type env =
    { persistent_set : (int, unit)Hashtbl.t
      mut_set : (int, unit)Hashtbl.t
      is_top : bool
      named_values : (int, Bir.bir_value)Hashtbl.t }

let empty_env() =
    { persistent_set = Hashtbl.create table_size
      is_top = true
      mut_set = Hashtbl.create table_size
      named_values = Hashtbl.create table_size }

let new_func_name() =
    let (id, _) = Var.newvar None
    "f" ^ string id

let mangle_func_name id = "f" ^ string id
let mangle_name id = "v" ^ string id
