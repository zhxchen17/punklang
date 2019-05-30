module Subst

module V = Var

open ir.Ast

(* substXMain m s n l exp
 * if    |s| = n
 * then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
 *)

let rec subst_kind_main m s n l k =
    match k with
    | Ktype -> k
    | Ksing c -> Ksing(subst_con_main m s n l c)
    | Kpi(k0, k1) ->
        Kpi(subst_kind_main m s n l k0, subst_kind_main (m + 1) s n l k1)
    | Kunit -> k

and subst_con_main m s n l c =
    match c with
    | Cvar i ->
        if i < m then c
        else if i < m + n then subst_con_main 0 [] 0 m (List.nth s (i - m))
        else Cvar(i - n + l)
    | Capp(c0, c1) -> Capp(subst_con_main m s n l c0, subst_con_main m s n l c1)
    | Clam(k, c) ->
        Clam(subst_kind_main m s n l k, subst_con_main (m + 1) s n l c)
    | Cunit -> c
    | Carrow(``params``, cr) ->
        Carrow
            (List.map (subst_con_main m s n l) ``params``,
             subst_con_main m s n l cr)
    | Cprod(cl, x_opt) -> Cprod(List.map (subst_con_main m s n l) cl, x_opt)
    | Cnamed(v, c) -> Cnamed(v, subst_con_main m s n l c)
    | Cref c -> Cref(subst_con_main m s n l c)
    | Cint
    | Cstring
    | Cbool -> c
    | Cforall(k, c) ->
        Cforall(subst_kind_main m s n l k, subst_con_main (m + 1) s n l c)
    | Carray c' -> Carray(subst_con_main m s n l c')

let rec subst_iface_main m s n l t =
    match t with
    | Iplam(k, t0, t1) ->
        Iplam
            (subst_kind_main m s n l k, subst_iface_main m s n l t0,
             subst_iface_main (m + 1) s n l t1)
    | Ivoid -> t
    | Imthds(name, cl, c) ->
        Imthds
            (name, List.map (subst_con_main m s n l) cl,
             subst_con_main m s n l c)

let rec subst_expr_main m s n l e =
    let subst_texp i (t, e) =
        (subst_con_main (m + i) s n l t, subst_expr_main (m + i) s n l e)
    match e with
    | Evar _ -> e
    | Efunc(``params``, c, st) ->
        Efunc
            (List.map (fun (v, mu, c) -> (v, mu, (subst_con_main m s n l c)))
                 ``params``, subst_con_main m s n l c,
             subst_stmt_main m s n l st)
    | Eint _
    | Estring _
    | Ebool _ -> e
    | Eop(o, tel) -> Eop(o, (List.map (subst_texp 0) tel))
    | Eapp(e, tel) -> Eapp(subst_texp 0 e, List.map (subst_texp 0) tel)
    | Etuple el -> Etuple(List.map (subst_texp 0) el)
    | Ector(c, sel) ->
        Ector
            (subst_con_main m s n l c,
             List.map (fun (x, e) -> (x, subst_texp 0 e)) sel)
    | Econ c -> Econ(subst_con_main m s n l c)
    | Eplam(k, t, te) ->
        Eplam
            (subst_kind_main m s n l k, subst_iface_main m s n l t,
             subst_texp 1 te)
    | Earray(c, el) ->
        Earray(subst_con_main m s n l c, List.map (subst_texp 0) el)
    | Efield(e, i) -> Efield(subst_texp 0 e, i)

and subst_stmt_main m s n l st =
    let subst_texp (t, e) =
        (subst_con_main m s n l t, subst_expr_main m s n l e)
    match st with
    | Sexpr e -> Sexpr(subst_texp e)
    | Sblk sl -> Sblk(List.map (subst_stmt_main m s n l) sl)
    | Sret e -> Sret(subst_texp e)
    | Sif(e, s0, s1) ->
        Sif
            (subst_texp e, subst_stmt_main m s n l s0,
             subst_stmt_main m s n l s1)
    | Swhile(e, st) -> Swhile(subst_texp e, subst_stmt_main m s n l st)
    | Sdecl(v, mu, e) -> Sdecl(v, mu, subst_texp e)
    | Sasgn(v, e) -> Sasgn(v, subst_texp e)

let subst_kind s x = subst_kind_main 0 [ s ] 1 0 x
let subst_con s x = subst_con_main 0 [ s ] 1 0 x
let subst_expr s x = subst_expr_main 0 [ s ] 1 0 x

let lift_kind l x =
    if l = 0 then x
    else subst_kind_main 0 [] 0 l x

let lift_con l x =
    if l = 0 then x
    else subst_con_main 0 [] 0 l x

let lift_expr l x =
    if l = 0 then x
    else subst_expr_main 0 [] 0 l x
