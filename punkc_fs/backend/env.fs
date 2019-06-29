module Env

open Config
open System.Collections.Generic
open Errors

type env =
    { mut_set : Dictionary<int, unit>
      named_refs : Dictionary<int, Bir.bir_value>
      struct_def : Dictionary<int, (string * ir.Ir.ty) list> }

let empty_env() =
    { mut_set = new Dictionary<_, _>()
      named_refs = new Dictionary<_, _>()
      struct_def = new Dictionary<_, _>() }

let new_func_name() =
    let (id, _) = Var.newvar None
    "f" + string id

let mangle_func_name id = "f" + string id
let mangle_name id = "v" + string id

let lookup_struct env id =
    match env.struct_def.TryGetValue(id) with
    | false, _ -> raise (BackendError "TODO lookup_struct")
    | true, stl -> stl
