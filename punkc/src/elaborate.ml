open Ast
open Utils

let rec elab_con env con =
  match con with
  | Cprod (cl, ll) -> Cprod (List.map (elab_con env) cl, ll)
  | Carrow (cpl, cr) ->
    Carrow (List.map (elab_con env) cpl, elab_con env cr)
  | Clam (k, c) -> Clam (elab_kind env k, elab_con env c)
  | Cref c -> Cref (elab_con env c)
  | Cnamed (v, Some c) -> Cnamed (v, Some (elab_con env c))
  | Cnamed ((id, x), None) ->
    begin match Hashtbl.find env.Env.elab_con_map id with
      | Cnamed ((i, _), Some c') ->
        assert (i = id);
        Cnamed ((id, x), Some c')
      | _ -> raise (Fatal "type name mapped to anonymous type")
    end
  | Cforall (k, c) -> Cforall (elab_kind env k, elab_con env c)
  | Capp (c0, c1) -> Capp (elab_con env c0, elab_con env c1)
  | Cunit -> con
  | Cint -> con
  | Cstring -> con
  | Cbool -> con
  | Cvar _ -> con
  | Carray (c, x) -> Carray (elab_con env c, x)

and elab_kind env kind =
  match kind with
  | Ksing c -> Ksing (elab_con env c)
  | Kpi (k0, k1) -> Kpi (elab_kind env k0, elab_kind env k1)
  | Kunit -> kind
  | Ktype -> kind

and elab_tcls env tcls =
  match tcls with
  | Tplam (k, t0, t1) ->
    Tplam (elab_kind env k, elab_tcls env t0, elab_tcls env t1)
  | Tmthds (s, cpl, cr) ->
    Tmthds (s, List.map (elab_con env) cpl, elab_con env cr)
  | Tvoid -> Tvoid

let rec elab_expr env expr =
  match expr with
  | Evar _ -> expr
  | Eop (o, el) -> Eop (o, List.map (elab_expr env) el)
  | Efunc (params, ret, s) ->
    Efunc (List.map (fun (x, m, c) -> (x, m, elab_con env c)) params,
           elab_con env ret,
           elab_stmt env s)
  | Etuple (x, el) ->
    Etuple (Option.map x (List.map (elab_con env)),
            List.map (elab_expr env) el)
  | Ector (c, sel) ->
    Ector (elab_con env c,
           List.map (fun (s, e) -> (s, elab_expr env e)) sel)
  | Econ c -> Econ (elab_con env c)
  | Eplam (k, t, e) ->
    Eplam (elab_kind env k, elab_tcls env t, elab_expr env e)
  | Eapp (e, params) ->
    Eapp (elab_expr env e, List.map (elab_expr env) params)
  | Eint _ -> expr
  | Estring _ -> expr
  | Ebool _ -> expr
  | Earray (None, el) ->
    Earray (None,  List.map (elab_expr env) el)
  | Earray (Some _, _) -> raise (Fatal "assuming untyped array literal")
  | Efield (e, i) -> Efield (elab_expr env e, i)

and elab_stmt env stmt =
  match stmt with
  | Sexpr e -> Sexpr (elab_expr env e)
  | Sblk sl ->
    Sblk (List.map (elab_stmt env) sl)
  | Sret e -> Sret (elab_expr env e)
  | Sif (e, s0, s1) ->
    Sif (elab_expr env e, elab_stmt env s0, elab_stmt env s1)
  | Swhile (e, s) -> Swhile (elab_expr env e, elab_stmt env s)
  | Sdecl ((id, _) as v, m, x, Econ c) ->
    let c' = elab_con env c in
    Hashtbl.add env.Env.elab_con_map id c';
    Sdecl (v, m, x, Econ c')
  | Sdecl (v, m, x, e) ->
    Sdecl (v, m, x, elab_expr env e)
  | Sasgn (p, e) -> Sasgn (elab_expr env p, elab_expr env e)
