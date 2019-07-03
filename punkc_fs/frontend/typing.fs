module Typing

open ir.Ir
open Errors

let rec whreduce c =
    match c with
    | Capp(c0, cl) ->
        (match whreduce c0 with
         | Clam(_, c0') -> whreduce (Subst.substlCon cl c0')
         | c0' -> Capp(c0', cl))
    | _ -> c

let rec whnf ctx c = whreduce c

let rec equiv ctx c0 c1 k =
    match k with
    | Ktype ->
        equivPath ctx (whnf ctx c0) (whnf ctx c1) |> ignore
        ()
    | Kpi(il, k1) ->
        let ctx' = List.fold (fun e _ -> Env.extendKind e Ktype) ctx il
        let len = List.length il
        let bnd = List.mapi (fun i _ -> Cvar i) il
        equiv ctx' (Capp(Subst.liftCon len c0, bnd))
            (Capp(Subst.liftCon len c1, bnd)) k1

and equivPath ctx c0 c1 =
    match (c0, c1) with
    | (Cvar i0, Cvar i1) ->
        if i0 = i1 then Env.lookupKind ctx i0
        else raise (TypeError "TODO equivPath")
    | (Capp(c0a, c0b), Capp(c1a, c1b)) ->
        (match equivPath ctx c0a c1a with
         | Kpi(kl0, k1) ->
             List.map3 (equiv ctx) c0b c1b kl0 |> ignore
             k1
         | _ -> raise (TypeError "TODO equivPath"))
    | (Carrow(c0a, c0b), Carrow(c1a, c1b)) ->
        List.iter2 (fun a b -> equiv ctx a b Ktype) c0a c1a
        equiv ctx c0b c1b Ktype
        Ktype
    | (Cforall(il0, c0'), Cforall(il1, c1')) ->
        List.iter2 (sameIface ctx) il0 il1
        let ctx' = List.fold (fun e _ -> Env.extendKind e Ktype) ctx il0
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
        if id0 = id1 then Env.lookupStruct ctx id0
        else raise (Error "TODO equivPath")
    | _ -> raise (EquivTypeError("TODO equivPath", string c0, string c1))

and sameIface ctx i0 i1 =
    match (i0, i1) with
    | (Inamed(id0, _), Inamed(id1, _)) ->
        if id0 = id1 then ()
        else raise (TypeError "TODO sameIface")
    | (Itop, Itop) -> ()
    | _ -> raise (TypeError "TODO sameIface")

and sameKind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        List.iter2 (sameKind ctx) k1a k1a
        let ctx' = List.fold (fun e k -> Env.extendKind e k) ctx k1a
        sameKind ctx' k0b k1b
    | _ -> raise (TypeError "TODO sameKind")

let rec subKind ctx k0 k1 =
    match (k0, k1) with
    | (Ktype, Ktype) -> ()
    | (Kpi(k0a, k0b), Kpi(k1a, k1b)) ->
        List.iter2 (subKind ctx) k1a k0a
        let ctx' = List.fold (fun e k -> Env.extendKind e k) ctx k1a
        subKind ctx' k0b k1b
    | _ -> raise (TypeError "TODO subkind")

let rec subType ctx t0 t1 =
    equiv ctx t0 t1 Ktype // FIXME
