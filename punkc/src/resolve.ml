open Tir
open Utils

let rec resolve_con env con =
  match con with
  | Tcon_prod (cl, ll) -> Tcon_prod (List.map (resolve_con env) cl, ll)
  | Tcon_arrow (cpl, cr) ->
    Tcon_arrow (List.map (resolve_con env) cpl, resolve_con env cr)
  | Tcon_lam (k, c) -> Tcon_lam (resolve_kind env k, resolve_con env c)
  | Tcon_ref c -> Tcon_ref (resolve_con env c)
  | Tcon_named ((i, Some x), c) when i < 0 ->
    assert (i = -1);
    begin match Env.find_id_opt env x with
      | Some id ->
        Tcon_named ((id, Some x), Option.map c (resolve_con env))
      | None -> raise (Error "undeclared type name")
    end
  | Tcon_forall (k, c) -> Tcon_forall (resolve_kind env k, resolve_con env c)
  | Tcon_named (a, c) -> Tcon_named (a, Option.map c (resolve_con env))
  | Tcon_app (c0, c1) -> Tcon_app (resolve_con env c0, resolve_con env c1)
  | Tcon_unit -> con
  | Tcon_int -> con
  | Tcon_string -> con
  | Tcon_bool -> con
  | Tcon_var _ -> con
  | Tcon_array (c, x) -> Tcon_array (resolve_con env c, x)

and resolve_kind env kind =
  match kind with
  | Tkind_sing c -> Tkind_sing (resolve_con env c)
  | Tkind_pi (k0, k1) -> Tkind_pi (resolve_kind env k0, resolve_kind env k1)
  | Tkind_unit -> kind
  | Tkind_type -> kind

and resolve_iface env iface =
  match iface with
  | Tiface_plam (k, t0, t1) ->
    Tiface_plam (resolve_kind env k, resolve_iface env t0, resolve_iface env t1)
  | Tiface_mthds (s, cpl, cr) ->
    Tiface_mthds (s, List.map (resolve_con env) cpl, resolve_con env cr)
  | Tiface_void -> Tiface_void

let rec resolve_expr env expr =
  match expr with
  | Texpr_var (-1, Some x) -> Texpr_var (Env.StringMap.find x env.Env.var_id_map, Some x)
  | Texpr_var (_, Some x) -> raise (Fatal "id is negative")
  | Texpr_op (o, el) -> Texpr_op (o, List.map (resolve_expr env) el)
  | Texpr_func (params, ret, s) ->
    let update_id env ((id, s), _, _) =
      Option.value_map s ~default:env ~f:(Env.add_id env id) in
    let env' = List.fold_left update_id env params in
    Texpr_func (List.map (fun (x, m, c) -> (x, m, resolve_con env c)) params,
           resolve_con env ret,
           resolve_stmt env' s)
  | Texpr_tuple (x, el) ->
    Texpr_tuple (Option.map x (List.map (resolve_con env)),
            List.map (resolve_expr env) el)
  | Texpr_ctor (c, sel) ->
    Texpr_ctor (resolve_con env c,
           List.map (fun (s, e) -> (s, resolve_expr env e)) sel)
  | Texpr_con c -> Texpr_con (resolve_con env c)
  | Texpr_plam (k, t, e) ->
    Texpr_plam (resolve_kind env k, resolve_iface env t, resolve_expr env e)
  | Texpr_app (e, params) ->
    Texpr_app (resolve_expr env e, List.map (resolve_expr env) params)
  | Texpr_int _ -> expr
  | Texpr_string _ -> expr
  | Texpr_bool _ -> expr
  | Texpr_var (_, None) -> expr
  | Texpr_array (None, el) ->
    Texpr_array (None, List.map (resolve_expr env) el)
  | Texpr_array (Some _, _) -> raise (Fatal "assuming untyped array literal")
  | Texpr_field (e, i) -> Texpr_field (resolve_expr env e, i)

and resolve_stmt env stmt =
  match stmt with
  | Tstmt_expr e -> Tstmt_expr (resolve_expr env e)
  | Tstmt_blk sl ->
    let update_id (env, sl) s =
      match s with
      | Tstmt_decl ((id, Some x), _, _, e) when id >= 0 ->
        (Env.add_id env id x, sl @ [resolve_stmt env s])
      | Tstmt_decl ((id, _), _, _, _) when id < 0 -> raise (Fatal "id is negative")
      | _ -> (env, sl @ [resolve_stmt env s]) in
    let _, sl' = List.fold_left update_id (env, []) sl in
    Tstmt_blk sl'
  | Tstmt_ret e -> Tstmt_ret (resolve_expr env e)
  | Tstmt_if (e, s0, s1) ->
    Tstmt_if (resolve_expr env e, resolve_stmt env s0, resolve_stmt env s1)
  | Tstmt_while (e, s) -> Tstmt_while (resolve_expr env e, resolve_stmt env s)
  | Tstmt_decl (v, m, Some c, e) ->
    Tstmt_decl (v, m, Some (resolve_con env c), resolve_expr env e)
  | Tstmt_decl (v, m, None, e) -> Tstmt_decl (v, m, None, resolve_expr env e)
  | Tstmt_asgn (p, e) -> Tstmt_asgn (resolve_expr env p, resolve_expr env e)
