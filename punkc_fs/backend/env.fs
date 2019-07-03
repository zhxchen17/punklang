module Env

open Config
open System.Collections.Generic
open Errors

type env =
    { mut_set : Dictionary<int, unit>
      named_refs : Dictionary<int, Bir.BirValue>
      struct_def : Dictionary<int, (string * ir.Ir.ty) list> }

let emptyEnv() =
    { mut_set = new Dictionary<_, _>()
      named_refs = new Dictionary<_, _>()
      struct_def = new Dictionary<_, _>() }

let newFuncName() =
    let (id, _) = Var.newvar None
    "f" + string id

let mangleFuncName id = "f" + string id
let mangleName id = "v" + string id

let lookupStruct env id =
    match env.struct_def.TryGetValue(id) with
    | false, _ -> raise (BackendError "TODO lookupStruct")
    | true, stl -> stl
