module Equiv

open ir.Ast
open Errors

let rec natural_kind ctx c =
    match c with
    | Cvar i -> Env.lookup_kind ctx i
    | Carrow _ -> Ktype
    | Cprod _ -> Ktype
    | Cref _ -> Ktype
    | Cnamed(v, c) -> natural_kind ctx c
    | Cunit -> Ktype
    | Cint -> Ktype
    | Capp(c0, c1) ->
        (match natural_kind ctx c0 with
         | Kpi(k0, k1) -> Subst.subst_kind c1 k1
         | _ -> raise (TypeError "natural_kind"))
    | Cforall _ -> Ktype
    | Carray _ -> Ktype
    | Cstring -> Ktype
    | Cbool -> Ktype
    | _ -> raise (TypeError "natural_kind")

let rec whreduce c =
    match c with
    | Capp(c0, c1) ->
        (match whreduce c0 with
         | Clam(_, c0') -> whreduce (Subst.subst_con c1 c0')
         | c0' -> Capp(c0', c1))
    | _ -> c

let rec whnf ctx c =
    let c' = whreduce c
    match natural_kind ctx c' with
    | Ksing c'' -> whnf ctx c''
    | _ -> c'

let rec equiv ctx c0 c1 k =
    match k with
    | Ktype ->
        let _ = equiv_path ctx (whnf ctx c0) (whnf ctx c1) in ()
    | Ksing _ -> ()
    | Kpi(k0, k1) ->
        equiv (Env.extend_kind ctx k0) (Capp(Subst.lift_con 1 c0, Cvar 0))
            (Capp(Subst.lift_con 1 c1, Cvar 0)) k1
    | Kunit -> ()

and equiv_path ctx c0 c1 =
    match (c0, c1) with
    | (Cvar i0, Cvar i1) ->
        if i0 = i1 then Env.lookup_kind ctx i0
        else raise (TypeError "equiv_path")
    | (Capp(c0a, c0b), Capp(c1a, c1b)) ->
        (match equiv_path ctx c0a c1a with
         | Kpi(k0, k1) ->
             equiv ctx c0b c1b k0
             Subst.subst_kind c0b k1
         | _ -> raise (TypeError "equiv_path"))
    | (Carrow(c0a, c0b), Carrow(c1a, c1b)) ->
        List.iter2 (fun a b -> equiv ctx a b Ktype) c0a c1a
        equiv ctx c0b c1b Ktype
        Ktype
    | (Cforall(k0, c0'), Cforall(k1, c1')) ->
        same_kind ctx k0 k1
        equiv (Env.extend_kind ctx k0) c0' c1' Ktype
        Ktype
    | (Cprod(cl0, None), Cprod(cl1, None)) ->
        List.iter2 (fun c0 c1 -> equiv ctx c0 c1 Ktype) cl0 cl1
        Ktype
    | (Cref c0', Cref c1') ->
        equiv ctx c0' c1' Ktype
        Ktype
    | (Cint, Cint) -> Ktype
    | (Cstring, Cstring) -> Ktype
    | (Cbool, Cbool) -> Ktype
    | (Cunit, Cunit) -> Ktype
    | (Carray c0', Carray c1') ->
        equiv ctx c0' c1' Ktype
        Ktype
    | (Cnamed((id0, _), _), Cnamed((id1, _), _)) ->
        (* TODO sometimes not Ktype when comparing HKT *)
        if id0 = id1 then Ktype
        else raise (Error "unmatched type name")
    | _ -> raise (EquivTypeError("equiv_path", string c0, string c1))

and same_kind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Ksing c0, Ksing c1) -> equiv ctx c0 c1 Ktype
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        same_kind ctx k1a k1a
        same_kind (Env.extend_kind ctx k1a) k0b k1b
    | (Kunit, Kunit) -> ()
    | _ -> raise (TypeError "same_kind")

let rec subkind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Ksing c0, Ksing c1) -> equiv ctx c0 c1 Ktype
    | (Ksing _, Ktype) -> ()
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        subkind ctx k1a k0a
        subkind (Env.extend_kind ctx k1a) k0b k1b
    | (Kunit, Kunit) -> ()
    | _ -> raise (TypeError "subkind")

let rec selfify c k =
    match k with
    | Ktype -> Ksing c
    | Ksing _ -> k
    | Kpi(k0, k1) -> Kpi(k1, selfify (Capp(Subst.lift_con 1 c, Cvar 0)) k1)
    | Kunit -> k

let rec inhabitant k =
    match k with
    | Ktype -> Cprod([], None)
    | Ksing c -> c
    | Kpi(k0, k1) -> Clam(k0, inhabitant k1)
    | Kunit -> Cunit
