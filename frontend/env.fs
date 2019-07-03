module Env

open Microsoft.FSharp.Collections
open System.Collections.Generic
open Config
open Errors

type context =
    { ksize : int
      kctx : ir.Ir.kind list
      tctx : Dictionary<int, int * ir.Ir.ty>
      struct_map : Dictionary<int, ir.Ir.kind> }

type env =
    { var_id_map : Map<string, int>
      ctx : context
      is_top : bool
      elab_con_map : Dictionary<int, Tir.con>
      struct_def : Dictionary<int, (string * ir.Ir.ty) list> }

let emptyCtx() =
    { ksize = 0
      kctx = []
      tctx = new Dictionary<_, _>()
      struct_map = new Dictionary<_, _>() }

let emptyEnv() =
    { var_id_map = Map.empty
      ctx = emptyCtx()
      is_top = true
      elab_con_map = new Dictionary<_, _>()
      struct_def = new Dictionary<_, _>() }

let addId env id name =
    { env with var_id_map = Map.add name id env.var_id_map }

let tryFindId env name = Map.tryFind name env.var_id_map

let lookupKind (ctx : context) i = List.item i ctx.kctx

let lookupType (ctx : context) v =
    match ctx.tctx.TryGetValue(v) with
    | true, (n, c) -> Subst.liftCon (ctx.ksize - n) c
    | false, _ -> raise (TypeError("TODO lookupType"))

let lookupStruct (ctx : context) i =
    match ctx.struct_map.TryGetValue(i) with
    | false, _ -> raise (TypeError "TODO lookupStruct")
    | true, v -> v

let extendKind (ctx : context) k =
    { struct_map = ctx.struct_map
      ksize = ctx.ksize + 1
      kctx = k :: ctx.kctx
      tctx = ctx.tctx }

let extendType (ctx : context) v c =
    ctx.tctx.Add(v, (ctx.ksize, c))

let ksize (ctx : context) = ctx.ksize
