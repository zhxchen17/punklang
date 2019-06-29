module Resolve

open Tir
open Errors

let value_map x d f =
    match x with
    | Some x' -> f x'
    | None -> d

let rec resolve_con env con =
    match con with
    | Tcon_prod(cl, ll) -> Tcon_prod(List.map (resolve_con env) cl, ll)
    | Tcon_arrow(cpl, cr) ->
        Tcon_arrow(List.map (resolve_con env) cpl, resolve_con env cr)
    | Tcon_ref c -> Tcon_ref(resolve_con env c)
    | Tcon_named(i, Some x) when i < 0 ->
        assert (i = -1)
        (match Env.find_id_opt env x with
         | Some id -> Tcon_named(id, Some x)
         | None -> raise (Error "undeclared type name"))
    | Tcon_named a -> Tcon_named a
    | Tcon_app(c0, c1) -> Tcon_app(resolve_con env c0, resolve_con env c1)
    | Tcon_unit -> con
    | Tcon_int -> con
    | Tcon_string -> con
    | Tcon_bool -> con
    | Tcon_var _ -> con
    | Tcon_array c -> Tcon_array(resolve_con env c)

let rec resolve_expr (env : Env.env) expr =
    match expr with
    | Texpr_var(-1, Some x) -> Texpr_var(Map.find x env.var_id_map, Some x)
    | Texpr_var(_, Some x) -> raise (Fatal "id should be negative")
    | Texpr_op(o, el) -> Texpr_op(o, List.map (resolve_expr env) el)
    | Texpr_func(args, ret, s) ->
        let update_id env ((id, s), _) = value_map s env (Env.add_id env id)
        let env' = List.fold update_id env args
        Texpr_func
            (List.map (fun (x, c) -> (x, resolve_con env c)) args,
             resolve_con env ret, resolve_stmt env' s)
    | Texpr_tuple el -> Texpr_tuple(List.map (resolve_expr env) el)
    | Texpr_ctor(c, sel) ->
        Texpr_ctor
            (resolve_con env c,
             List.map (fun (s, e) -> (s, resolve_expr env e)) sel)
    | Texpr_con c -> Texpr_con(resolve_con env c)
    | Texpr_app(e, args) ->
        Texpr_app(resolve_expr env e, List.map (resolve_expr env) args)
    | Texpr_int _ -> expr
    | Texpr_string _ -> expr
    | Texpr_bool _ -> expr
    | Texpr_var(_, None) -> expr
    | Texpr_array el -> Texpr_array(List.map (resolve_expr env) el)
    | Texpr_field(e, i) -> Texpr_field(resolve_expr env e, i)

and resolve_stmt env stmt =
    match stmt with
    | Tstmt_expr e -> Tstmt_expr(resolve_expr env e)
    | Tstmt_blk sl ->
        let update_env env s =
            match s with
            | Tstmt_decl((id, Some x), _, _, e) when id >= 0 ->
                Env.add_id env id x
            | Tstmt_decl((id, _), _, _, _) when id < 0 ->
                raise (Fatal "id is negative")
            | _ -> env
        Tstmt_blk(Visitors.visit_block env update_env resolve_stmt sl)
    | Tstmt_ret e -> Tstmt_ret(resolve_expr env e)
    | Tstmt_if(e, s0, s1) ->
        Tstmt_if(resolve_expr env e, resolve_stmt env s0, resolve_stmt env s1)
    | Tstmt_while(e, s) -> Tstmt_while(resolve_expr env e, resolve_stmt env s)
    | Tstmt_decl(v, m, Some c, e) ->
        Tstmt_decl(v, m, Some(resolve_con env c), resolve_expr env e)
    | Tstmt_decl(v, m, None, e) -> Tstmt_decl(v, m, None, resolve_expr env e)
    | Tstmt_asgn(p, e) -> Tstmt_asgn(resolve_expr env p, resolve_expr env e)
