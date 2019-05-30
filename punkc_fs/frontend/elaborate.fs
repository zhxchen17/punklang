module Elaborate

module Hashtbl = FSharp.Compatibility.OCaml.Hashtbl

open Tir
open Errors

let rec elab_con env con =
    match con with
    | Tcon_prod(cl, ll) -> Tcon_prod(List.map (elab_con env) cl, ll)
    | Tcon_arrow(cpl, cr) ->
        Tcon_arrow(List.map (elab_con env) cpl, elab_con env cr)
    | Tcon_lam(k, c) -> Tcon_lam(elab_kind env k, elab_con env c)
    | Tcon_ref c -> Tcon_ref(elab_con env c)
    | Tcon_named v -> Tcon_named v
    | Tcon_forall(k, c) -> Tcon_forall(elab_kind env k, elab_con env c)
    | Tcon_app(c0, c1) -> Tcon_app(elab_con env c0, elab_con env c1)
    | Tcon_unit -> con
    | Tcon_int -> con
    | Tcon_string -> con
    | Tcon_bool -> con
    | Tcon_var _ -> con
    | Tcon_array c -> Tcon_array(elab_con env c)

and elab_kind env kind =
    match kind with
    | Tkind_sing c -> Tkind_sing(elab_con env c)
    | Tkind_pi(k0, k1) -> Tkind_pi(elab_kind env k0, elab_kind env k1)
    | Tkind_unit -> kind
    | Tkind_type -> kind

and elab_iface env iface =
    match iface with
    | Tiface_plam(k, t0, t1) ->
        Tiface_plam(elab_kind env k, elab_iface env t0, elab_iface env t1)
    | Tiface_mthds(s, cpl, cr) ->
        Tiface_mthds(s, List.map (elab_con env) cpl, elab_con env cr)
    | Tiface_void -> Tiface_void

let rec elab_expr env expr =
    match expr with
    | Texpr_var _ -> expr
    | Texpr_op(o, el) -> Texpr_op(o, List.map (elab_expr env) el)
    | Texpr_func(``params``, ret, s) ->
        Texpr_func
            (List.map (fun (x, m, c) -> (x, m, elab_con env c)) ``params``,
             elab_con env ret, elab_stmt env s)
    | Texpr_tuple el -> Texpr_tuple(List.map (elab_expr env) el)
    | Texpr_ctor(c, sel) ->
        Texpr_ctor
            (elab_con env c, List.map (fun (s, e) -> (s, elab_expr env e)) sel)
    | Texpr_con c -> Texpr_con(elab_con env c)
    | Texpr_plam(k, t, e) ->
        Texpr_plam(elab_kind env k, elab_iface env t, elab_expr env e)
    | Texpr_app(e, ``params``) ->
        Texpr_app(elab_expr env e, List.map (elab_expr env) ``params``)
    | Texpr_int _ -> expr
    | Texpr_string _ -> expr
    | Texpr_bool _ -> expr
    | Texpr_array el -> Texpr_array(List.map (elab_expr env) el)
    | Texpr_field(e, i) -> Texpr_field(elab_expr env e, i)

and elab_stmt (env : Env.env) stmt =
    match stmt with
    | Tstmt_expr e -> Tstmt_expr(elab_expr env e)
    | Tstmt_blk sl -> Tstmt_blk(List.map (elab_stmt env) sl)
    | Tstmt_ret e -> Tstmt_ret(elab_expr env e)
    | Tstmt_if(e, s0, s1) ->
        Tstmt_if(elab_expr env e, elab_stmt env s0, elab_stmt env s1)
    | Tstmt_while(e, s) -> Tstmt_while(elab_expr env e, elab_stmt env s)
    | Tstmt_decl((id, _) as v, m, x, Texpr_con c) ->
        let c' = elab_con env c
        Hashtbl.add env.elab_con_map id c'
        Tstmt_decl(v, m, x, Texpr_con c')
    | Tstmt_decl(v, m, x, e) -> Tstmt_decl(v, m, x, elab_expr env e)
    | Tstmt_asgn(p, e) -> Tstmt_asgn(elab_expr env p, elab_expr env e)
