module Typing

open ir.Ir
open Errors

let rec whreduce c =
    match c with
    | Capp(c0, cl) ->
        (match whreduce c0 with
         | Clam(_, c0') -> whreduce (Subst.substl_con cl c0')
         | c0' -> Capp(c0', cl))
    | _ -> c

let rec whnf ctx c = whreduce c

let rec equiv ctx c0 c1 k =
    match k with
    | Ktype ->
        equiv_path ctx (whnf ctx c0) (whnf ctx c1) |> ignore
        ()
    | Kpi(il, k1) ->
        let ctx' = List.fold (fun e _ -> Env.extend_kind e Ktype) ctx il
        let len = List.length il
        let bnd = List.mapi (fun i _ -> Cvar i) il
        equiv ctx' (Capp(Subst.lift_con len c0, bnd))
            (Capp(Subst.lift_con len c1, bnd)) k1

and equiv_path ctx c0 c1 =
    match (c0, c1) with
    | (Cvar i0, Cvar i1) ->
        if i0 = i1 then Env.lookup_kind ctx i0
        else raise (TypeError "TODO equiv_path")
    | (Capp(c0a, c0b), Capp(c1a, c1b)) ->
        (match equiv_path ctx c0a c1a with
         | Kpi(kl0, k1) ->
             List.map3 (equiv ctx) c0b c1b kl0 |> ignore
             k1
         | _ -> raise (TypeError "TODO equiv_path"))
    | (Carrow(c0a, c0b), Carrow(c1a, c1b)) ->
        List.iter2 (fun a b -> equiv ctx a b Ktype) c0a c1a
        equiv ctx c0b c1b Ktype
        Ktype
    | (Cforall(il0, c0'), Cforall(il1, c1')) ->
        List.iter2 (same_iface ctx) il0 il1
        let ctx' = List.fold (fun e _ -> Env.extend_kind e Ktype) ctx il0
        equiv ctx' c0' c1' Ktype
        Ktype
    | (Cprod cl0, Cprod cl1) ->
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
    | (Cstruct(id0, _), Cstruct(id1, _)) ->
        if id0 = id1 then Env.lookup_struct ctx id0
        else raise (Error "TODO equiv_path")
    | _ -> raise (EquivTypeError("TODO equiv_path", string c0, string c1))

and same_iface ctx i0 i1 =
    match (i0, i1) with
    | (Inamed(id0, _), Inamed(id1, _)) ->
        if id0 = id1 then ()
        else raise (TypeError "TODO same_iface")
    | (Itop, Itop) -> ()
    | _ -> raise (TypeError "TODO same_iface")

and same_kind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        List.iter2 (same_kind ctx) k1a k1a
        let ctx' = List.fold (fun e k -> Env.extend_kind e k) ctx k1a
        same_kind ctx' k0b k1b
    | _ -> raise (TypeError "TODO same_kind")

let rec subkind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        List.iter2 (subkind ctx) k1a k0a
        let ctx' = List.fold (fun e k -> Env.extend_kind e k) ctx k1a
        subkind ctx' k0b k1b
    | _ -> raise (TypeError "TODO subkind")

let rec subtype ctx t0 t1 =
    equiv ctx t0 t1 Ktype // FIXME
