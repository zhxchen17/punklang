open Ast
open Utils
module Option = Core.Option

let rec resolve_con env con =
  match con with
  | Cprod (cl, ll) -> Cprod (List.map (resolve_con env) cl, ll)
  | Carrow (cpl, cr) ->
    Carrow (List.map (resolve_con env) cpl, resolve_con env cr)
  | Clam (k, c) -> Clam (resolve_kind env k, resolve_con env c)
  | Cref c -> Cref (resolve_con env c)
  | Cnamed ((i, Some x), c) when i < 0 ->
    assert (i = -1);
    begin match Env.find_id_opt env x with
      | Some id ->
        Cnamed ((id, Some x), Option.map c (resolve_con env))
      | None -> raise (Error "undeclared type name")
    end
  | Cforall (k, c) -> Cforall (resolve_kind env k, resolve_con env c)
  | Cnamed (a, c) -> Cnamed (a, Option.map c (resolve_con env))
  | Capp (c0, c1) -> Capp (resolve_con env c0, resolve_con env c1)
  | Cunit -> con
  | Cint -> con
  | Cstring -> con
  | Cbool -> con
  | Cvar _ -> con
  | Carray (c, x) -> Carray (resolve_con env c, x)

and resolve_kind env kind =
  match kind with
  | Ksing c -> Ksing (resolve_con env c)
  | Kpi (k0, k1) -> Kpi (resolve_kind env k0, resolve_kind env k1)
  | Kunit -> kind
  | Ktype -> kind

and resolve_tcls env tcls =
  match tcls with
  | Tplam (k, t0, t1) ->
    Tplam (resolve_kind env k, resolve_tcls env t0, resolve_tcls env t1)
  | Tmthds (s, cpl, cr) ->
    Tmthds (s, List.map (resolve_con env) cpl, resolve_con env cr)
  | Tvoid -> Tvoid

let rec resolve_expr env expr =
  match expr with
  | Evar (-1, Some x) -> Evar (Env.StringMap.find x env.Env.var_id_map, Some x)
  | Evar (_, Some x) -> raise (Fatal "id is negative")
  | Eop (o, el) -> Eop (o, List.map (resolve_expr env) el)
  | Efunc (params, ret, s) ->
    let update_id env ((id, s), _, _) =
      Option.value_map s ~default:env ~f:(Env.add_id env id) in
    let env' = List.fold_left update_id env params in
    Efunc (List.map (fun (x, m, c) -> (x, m, resolve_con env c)) params,
           resolve_con env ret,
           resolve_stmt env' s)
  | Etuple (x, el) ->
    Etuple (Option.map x (List.map (resolve_con env)),
            List.map (resolve_expr env) el)
  | Ector (c, sel) ->
    Ector (resolve_con env c,
           List.map (fun (s, e) -> (s, resolve_expr env e)) sel)
  | Econ c -> Econ (resolve_con env c)
  | Eplam (k, t, e) ->
    Eplam (resolve_kind env k, resolve_tcls env t, resolve_expr env e)
  | Eapp (e, params) ->
    Eapp (resolve_expr env e, List.map (resolve_expr env) params)
  | Eint _ -> expr
  | Estring _ -> expr
  | Ebool _ -> expr
  | Evar (_, None) -> expr
  | Earray (None, el) ->
    Earray (None,  List.map (resolve_expr env) el)
  | Earray (Some _, _) -> raise (Fatal "assuming untyped array literal")
  | Efield (e, i) -> Efield (resolve_expr env e, i)

and resolve_stmt env stmt =
  match stmt with
  | Sexpr e -> Sexpr (resolve_expr env e)
  | Sblk sl ->
    let update_id (env, sl) s =
      match s with
      | Sdecl ((id, Some x), _, _, e) when id >= 0 ->
        (Env.add_id env id x, sl @ [resolve_stmt env s])
      | Sdecl ((id, _), _, _, _) when id < 0 -> raise (Fatal "id is negative")
      | _ -> (env, sl @ [resolve_stmt env s]) in
    let _, sl' = List.fold_left update_id (env, []) sl in
    Sblk sl'
  | Sret e -> Sret (resolve_expr env e)
  | Sif (e, s0, s1) ->
    Sif (resolve_expr env e, resolve_stmt env s0, resolve_stmt env s1)
  | Swhile (e, s) -> Swhile (resolve_expr env e, resolve_stmt env s)
  | Sdecl (v, m, Some c, e) ->
    Sdecl (v, m, Some (resolve_con env c), resolve_expr env e)
  | Sdecl (v, m, None, e) -> Sdecl (v, m, None, resolve_expr env e)
  | Sasgn (p, e) -> Sasgn (resolve_expr env p, resolve_expr env e)
