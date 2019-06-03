module Env

open Microsoft.FSharp.Collections
open System.Collections.Generic
open Config
open Errors

type context =
    { ksize : int
      kctx : ir.Ast.kind list
      tctx : Map<int, int * ir.Ast.ty> }

type env =
    { var_id_map : Map<string, int>
      ctx : context
      is_top : bool
      elab_con_map : Dictionary<int, Tir.con> }

let empty_ctx() =
    { ksize = 0
      kctx = []
      tctx = Map.empty }

let empty_env() =
    { var_id_map = Map.empty
      ctx = empty_ctx()
      is_top = true
      elab_con_map = new Dictionary<_, _>() }

let add_id env id name =
    { env with var_id_map = Map.add name id env.var_id_map }
let find_id_opt env name = Map.tryFind name env.var_id_map
let lookup_kind (ctx : context) i =
    Subst.lift_kind (i + 1) (List.item i ctx.kctx)

let lookup_type (ctx : context) v =
    match Map.tryFind v ctx.tctx with
    | Some(n, c) -> Subst.lift_con (ctx.ksize - n) c
    | None -> raise (TypeError("lookup_type: " + (string v)))

let extend_kind (ctx : context) k =
    { ksize = ctx.ksize + 1
      kctx = k :: ctx.kctx
      tctx = ctx.tctx }

let extend_type (ctx : context) v c =
    { ksize = ctx.ksize
      kctx = ctx.kctx
      tctx = Map.add v (ctx.ksize, c) ctx.tctx }

let ksize (ctx : context) = ctx.ksize
