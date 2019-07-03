module Resolve

open Tir
open Errors

let valueMap x d f =
    match x with
    | Some x' -> f x'
    | None -> d

let updateEnv env = function
    | Tstmt_decl((id, Some name), _, _, _) when id >= 0 ->
        Env.addId env id name
    | Tstmt_struct((id, Some name), _) when id >= 0 ->
        Env.addId env id name
    | Tstmt_decl((id, _), _, _, _) when id < 0 ->
        raise (Fatal "TODO resolveProg")
    | Tstmt_struct((id, _), _) when id < 0 ->
        raise (Fatal "TODO resolveProg")
    | _ -> env

let rec resolveCon env con =
    match con with
    | Tcon_prod(cl, ll) -> Tcon_prod(List.map (resolveCon env) cl, ll)
    | Tcon_arrow(cpl, cr) ->
        Tcon_arrow(List.map (resolveCon env) cpl, resolveCon env cr)
    | Tcon_ref c -> Tcon_ref(resolveCon env c)
    | Tcon_named(i, Some x) when i < 0 ->
        assert (i = -1)
        (match Env.tryFindId env x with
         | Some id -> Tcon_named(id, Some x)
         | None -> raise (Error "TODO resolveCon"))
    | Tcon_named a -> Tcon_named a
    | Tcon_app(c0, c1) -> Tcon_app(resolveCon env c0, resolveCon env c1)
    | Tcon_unit -> con
    | Tcon_int -> con
    | Tcon_string -> con
    | Tcon_bool -> con
    | Tcon_var _ -> con
    | Tcon_array c -> Tcon_array(resolveCon env c)

let rec resolveExpr (env : Env.env) expr =
    match expr with
    | Texpr_var(-1, Some x) ->
        Texpr_var(Map.find x env.var_id_map, Some x)
    | Texpr_var(_, Some x) -> raise (Fatal "TODO resolveExpr")
    | Texpr_op(o, el) -> Texpr_op(o, List.map (resolveExpr env) el)
    | Texpr_func(args, ret, s) ->
        let update_id env ((id, s), _) = valueMap s env (Env.addId env id)
        let env' = List.fold update_id env args
        Texpr_func
            (List.map (fun (x, c) -> (x, resolveCon env c)) args,
             resolveCon env ret, resolveStmt env' s)
    | Texpr_tuple el -> Texpr_tuple(List.map (resolveExpr env) el)
    | Texpr_ctor(c, sel) ->
        Texpr_ctor
            (resolveCon env c,
             List.map (fun (s, e) -> (s, resolveExpr env e)) sel)
    | Texpr_app(e, args) ->
        Texpr_app(resolveExpr env e, List.map (resolveExpr env) args)
    | Texpr_int _ -> expr
    | Texpr_string _ -> expr
    | Texpr_bool _ -> expr
    | Texpr_var(_, None) -> expr
    | Texpr_array el -> Texpr_array(List.map (resolveExpr env) el)
    | Texpr_field(e, i) -> Texpr_field(resolveExpr env e, i)

and resolveStmt env stmt =
    match stmt with
    | Tstmt_expr e -> Tstmt_expr(resolveExpr env e)
    | Tstmt_blk sl -> Tstmt_blk(resolveBlk env sl)
    | Tstmt_ret e -> Tstmt_ret(resolveExpr env e)
    | Tstmt_if(e, s0, s1) ->
        Tstmt_if(resolveExpr env e, resolveStmt env s0, resolveStmt env s1)
    | Tstmt_while(e, s) -> Tstmt_while(resolveExpr env e, resolveStmt env s)
    | Tstmt_decl(v, m, Some c, e) ->
        Tstmt_decl(v, m, Some(resolveCon env c), resolveExpr env e)
    | Tstmt_decl(v, m, None, e) -> Tstmt_decl(v, m, None, resolveExpr env e)
    | Tstmt_asgn(p, e) -> Tstmt_asgn(resolveExpr env p, resolveExpr env e)
    | Tstmt_struct(v, stl) ->
        let tl = List.map (snd >> (resolveCon env)) stl
        Tstmt_struct(v, List.zip (List.map fst stl) tl)

and resolveBlk env = function
    | [] -> []
    | hd :: tl ->
        let env' = updateEnv env hd
        (resolveStmt env hd) :: (resolveBlk env' tl)

let resolveModule env prog =
    let env' = List.fold updateEnv env prog
    List.map (resolveStmt env') prog

