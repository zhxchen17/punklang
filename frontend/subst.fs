module Subst

module V = Var

open ir.Ir

(* substXMain m s n l exp
 * if    |s| = n
 * then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
 *)

let rec substConMain m s n l c =
    match c with
    | Cvar i ->
        if i < m then c
        else if i < m + n then substConMain 0 [] 0 m (List.item (i - m) s)
        else Cvar(i - n + l)
    | Capp(c0, cl) ->
        Capp(substConMain m s n l c0, List.map (substConMain m s n l) cl)
    | Clam(il, c) ->
        let il' = List.map (substIfaceMain m s n l) il
        let len = List.length il
        Clam(il', substConMain (m + len) s n l c)
    | Cunit -> c
    | Carrow(args, cr) ->
        Carrow
            (List.map (substConMain m s n l) args,
             substConMain m s n l cr)
    | Cprod cl -> Cprod(List.map (substConMain m s n l) cl)
    | Cstruct v -> Cstruct v
    | Cref c -> Cref(substConMain m s n l c)
    | Cint
    | Cstring
    | Cbool -> c
    | Cforall(il, c) ->
        let il' = List.map (substIfaceMain m s n l) il
        let len = List.length il
        Cforall(il', substConMain (m + len) s n l c)
    | Carray c' -> Carray(substConMain m s n l c')
    | Csym _ -> c
    | Cexists(il, c) ->
        let il' = List.map (substIfaceMain m s n l) il
        let len = List.length il
        Cexists(il', substConMain (m + len) s n l c)

and substIfaceMain m s n l t =
    match t with
    | Inamed _ -> t
    | Itop _ -> t

let rec substExprMain m s n l e =
    let subst_texp i (t, e) =
        (substConMain (m + i) s n l t, substExprMain (m + i) s n l e)
    match e with
    | Evar _ -> e
    | Efunc(id, args, c, st) ->
        Efunc
            (id,
             List.map (fun (v, c) -> (v, (substConMain m s n l c)))
                 args, substConMain m s n l c,
             substStmtMain m s n l st)
    | Eint _
    | Estring _
    | Ebool _ -> e
    | Eop(o, tel) -> Eop(o, (List.map (subst_texp 0) tel))
    | Eapp(e, tel) -> Eapp(subst_texp 0 e, List.map (subst_texp 0) tel)
    | Etuple el -> Etuple(List.map (subst_texp 0) el)
    | Ector(c, sel) ->
        Ector
            (substConMain m s n l c,
             List.map (fun (x, e) -> (x, subst_texp 0 e)) sel)
    // | Eplam(k, t, te) ->
    // Eplam
    // (subst_kindMain m s n l k, substIfaceMain m s n l t,
    // subst_texp 1 te)
    | Earray el ->
        Earray(List.map (subst_texp 0) el)
    | Efield(e, i) -> Efield(subst_texp 0 e, i)
    | Edefault c -> Edefault(substConMain m s n l c)

and substStmtMain m s n l st =
    let substTexp (t, e) =
        (substConMain m s n l t, substExprMain m s n l e)
    match st with
    | Sexpr e -> Sexpr(substTexp e)
    | Sblk sl -> Sblk(List.map (substStmtMain m s n l) sl)
    | Sret e -> Sret(substTexp e)
    | Sif(e, s0, s1) ->
        Sif
            (substTexp e, substStmtMain m s n l s0,
             substStmtMain m s n l s1)
    | Swhile(e, st) -> Swhile(substTexp e, substStmtMain m s n l st)
    | Sdecl(v, e) -> Sdecl(v, substTexp e)
    | Sasgn(v, e) -> Sasgn(v, substTexp e)

let substCon s x = substConMain 0 [ s ] 1 0 x
let substExpr s x = substExprMain 0 [ s ] 1 0 x

let substlCon s x = substConMain 0 s (List.length s) 0 x
let substlExpr s x = substExprMain 0 s (List.length s) 0 x

let liftCon l x =
    if l = 0 then x
    else substConMain 0 [] 0 l x

let liftExpr l x =
    if l = 0 then x
    else substExprMain 0 [] 0 l x
