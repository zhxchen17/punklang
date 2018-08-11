open Ast

module V = Var

(* substXMain m s n l exp
 * if    |s| = n
 * then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
 *)

let rec subst_kind_main m s n l k =
  match k with
  | Ktype -> k
  | Ksing c -> Ksing (subst_con_main m s n l c)
  | Kpi (k0, k1) ->
    Kpi (subst_kind_main m s n l k0, subst_kind_main (m + 1) s n l k1)
  | Ksigma (k0, k1) ->
    Ksigma (subst_kind_main m s n l k0, subst_kind_main (m+1) s n l k1)
  | Kunit -> k

and subst_con_main m s n l c =
  match c with
  | Cvar i ->
    if i < m then
      c
    else if i < m + n then
      subst_con_main 0 [] 0 m (List.nth s (i - m))
    else
      Cvar (i - n + l)
  | Clam (k, c) ->
    Clam (subst_kind_main m s n l k, subst_con_main (m + 1) s n l c)
  | Cunit -> c
  | Carrow (params, cr) ->
    Carrow (List.map (subst_con_main m s n l) params, subst_con_main m s n l cr)
  | Cprod (cl, x_opt) -> Cprod (List.map (subst_con_main m s n l) cl, x_opt)
  | Cnamed (v, None) -> c
  | Cnamed (v, Some c) -> Cnamed (v, Some (subst_con_main m s n l c))
  | Cref c -> Cref (subst_con_main m s n l c)
  | Cint -> c

let rec subst_tcls_main m s n l t =
  match t with
  | Tplam (k, t0, t1) ->
    Tplam (subst_kind_main m s n l k,
           subst_tcls_main m s n l t0,
           subst_tcls_main (m + 1) s n l t1)
  | Tvoid -> t
  | Tmthds (name, cl, c) ->
    Tmthds (name, List.map (subst_con_main m s n l) cl, subst_con_main m s n l c)

let rec subst_expr_main m s n l e =
  match e with
  | Evar _ -> e
  | Efunc (params, c, st) ->
    Efunc (List.map (fun (v, c) -> (v, (subst_con_main m s n l c))) params,
           subst_con_main m s n l c,
           subst_stmt_main m s n l st)
  | Eint _ -> e
  | Eop (o, el) -> Eop (o, List.map (subst_expr_main m s n l) el)
  | Eapp (e, el) ->
    Eapp (subst_expr_main m s n l e, List.map (subst_expr_main m s n l) el)
  | Etuple el -> Etuple (List.map (subst_expr_main m s n l) el)
  | Econ c -> Econ (subst_con_main m s n l c)
  | Eplam (k, t, e) ->
    Eplam (subst_kind_main m s n l k,
           subst_tcls_main m s n l t,
           subst_expr_main (m + 1) s n l e)

and subst_stmt_main m s n l st =
  match st with
  | Sexpr e -> Sexpr (subst_expr_main m s n l e)
  | Sblk sl -> Sblk (List.map (subst_stmt_main m s n l) sl)
  | Sret e -> Sret (subst_expr_main m s n l e)
  | Sif (e, s0, s1) ->
    Sif (subst_expr_main m s n l e,
         subst_stmt_main m s n l s0,
         subst_stmt_main m s n l s1)
  | Swhile (e, st) ->
    Swhile (subst_expr_main m s n l e, subst_stmt_main m s n l st)
  | Sdecl (v, Some c, e) ->
    Sdecl (v, Some (subst_con_main m s n l c), subst_expr_main m s n l e)
  | Sdecl (v, None, e) -> Sdecl (v, None, subst_expr_main m s n l e)
  | Sasgn (v, e) -> Sasgn(v, subst_expr_main m s n l e)

let subst_kind s x = subst_kind_main 0 [s] 1 0 x
let subst_con s x = subst_con_main 0 [s] 1 0 x
let subst_expr s x = subst_expr_main 0 [s] 1 0 x

let lift_kind l x =
  if l = 0 then x else subst_kind_main 0 [] 0 l x
let lift_con l x =
  if l = 0 then x else subst_con_main 0 [] 0 l x
let lift_expr l x =
  if l = 0 then x else subst_expr_main 0 [] 0 l x
