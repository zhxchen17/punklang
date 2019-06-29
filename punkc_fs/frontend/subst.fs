module Subst

module V = Var

open ir.Ir

(* substXMain m s n l exp
 * if    |s| = n
 * then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
 *)

let rec subst_con_main m s n l c =
    match c with
    | Cvar i ->
        if i < m then c
        else if i < m + n then subst_con_main 0 [] 0 m (List.item (i - m) s)
        else Cvar(i - n + l)
    | Capp(c0, cl) ->
        Capp(subst_con_main m s n l c0, List.map (subst_con_main m s n l) cl)
    | Clam(il, c) ->
        let il' = List.map (subst_iface_main m s n l) il
        let len = List.length il
        Clam(il', subst_con_main (m + len) s n l c)
    | Cunit -> c
    | Carrow(args, cr) ->
        Carrow
            (List.map (subst_con_main m s n l) args,
             subst_con_main m s n l cr)
    | Cprod cl -> Cprod(List.map (subst_con_main m s n l) cl)
    | Cstruct v -> Cstruct v
    | Cref c -> Cref(subst_con_main m s n l c)
    | Cint
    | Cstring
    | Cbool -> c
    | Cforall(il, c) ->
        let il' = List.map (subst_iface_main m s n l) il
        let len = List.length il
        Cforall(il', subst_con_main (m + len) s n l c)
    | Carray c' -> Carray(subst_con_main m s n l c')
    | Csym _ -> c
    | Cexists(il, c) ->
        let il' = List.map (subst_iface_main m s n l) il
        let len = List.length il
        Cexists(il', subst_con_main (m + len) s n l c)

and subst_iface_main m s n l t =
    match t with
    | Inamed _ -> t
    | Itop _ -> t

let rec subst_expr_main m s n l e =
    let subst_texp i (t, e) =
        (subst_con_main (m + i) s n l t, subst_expr_main (m + i) s n l e)
    match e with
    | Evar _ -> e
    | Efunc(id, args, c, st) ->
        Efunc
            (id,
             List.map (fun (v, c) -> (v, (subst_con_main m s n l c)))
                 args, subst_con_main m s n l c,
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
    // | Eplam(k, t, te) ->
    // Eplam
    // (subst_kind_main m s n l k, subst_iface_main m s n l t,
    // subst_texp 1 te)
    | Earray el ->
        Earray(List.map (subst_texp 0) el)
    | Efield(e, i) -> Efield(subst_texp 0 e, i)
    | Edefault c -> Edefault(subst_con_main m s n l c)

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
    | Sdecl(v, e) -> Sdecl(v, subst_texp e)
    | Sasgn(v, e) -> Sasgn(v, subst_texp e)

let subst_con s x = subst_con_main 0 [ s ] 1 0 x
let subst_expr s x = subst_expr_main 0 [ s ] 1 0 x

let substl_con s x = subst_con_main 0 s (List.length s) 0 x
let substl_expr s x = subst_expr_main 0 s (List.length s) 0 x

let lift_con l x =
    if l = 0 then x
    else subst_con_main 0 [] 0 l x

let lift_expr l x =
    if l = 0 then x
    else subst_expr_main 0 [] 0 l x
