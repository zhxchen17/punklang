module Check

open ir.Ir
open Errors

let rec inferType (env : Env.env) = function
    | Cint -> Ktype
    | Cstring -> Ktype
    | Cbool -> Ktype
    | Cvar i ->
        if i >= env.ctx.ksize then
            raise (Fatal "TODO inferType")
        else
            Ktype
    | Cprod cl ->
        List.iter (checkType env Ktype) cl
        Ktype
    | Carrow(cl, c) ->
        List.iter (checkType env Ktype) cl
        checkType env Ktype c
        Ktype
    | Clam(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extendKind c Ktype) env.ctx il
        let k = inferType { env with ctx = ctx' } c
        let kl = List.init (List.length il) (fun _ -> Ktype)
        Kpi(kl, k)
    | Capp(c, cl) ->
        let k = inferType env c
        match k with
        | Kpi(l, r) ->
            List.iter2 (checkType env) l cl
            r
        | _ -> raise (TypeError "TODO inferType")
    | Cforall(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extendKind c Ktype) env.ctx il
        inferType { env with ctx = ctx' } c
    | Carray c ->
        inferType env c
    | Cref c ->
        inferType env c
    | Cstruct(i, _) ->
        match env.ctx.struct_map.TryGetValue(i) with
        | false, _ -> raise (Fatal "TODO inferType")
        | true, k -> k
    | Cunit ->
        Ktype
    | Csym _ ->
        raise (Fatal "TODO inferType")
    | Cexists(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extendKind c Ktype) env.ctx il
        inferType { env with ctx = ctx' } c

and checkType (env : Env.env) k c =
    let k' = inferType env c
    Typing.subKind env.ctx k' k

let scanHeader (env : Env.env) ((i, _), d) =
    match d with
    | Dstruct([], _) -> env.ctx.struct_map.Add(i, Ktype)
    | Dstruct(il, _) ->
        let len = List.length il
        env.ctx.struct_map.Add(i, Kpi(List.init len (fun _ -> Ktype), Ktype))
    | Diface _ -> raise (Fatal "TODO scanHeader")
    | Dalias _ -> raise (Fatal "TODO scanHeader")

let checkHeader (env : Env.env) ((i, _), d) =
    match d with
    | Dstruct(_, stl) ->
        List.iter (fun (_, t) -> checkType env Ktype t) stl
        env.struct_def.Add(i, stl)
    | Diface _ -> raise (Fatal "TODO checkHeader")
    | Dalias _ -> raise (Fatal "TODO checkHeader")

let rec checkStmt (env : Env.env) = function
    | Sexpr e ->
        Sexpr(inferExpr env e)
    | Sblk sl ->
        Sblk(checkStmts env sl)
    | Sret e ->
        Sret(inferExpr env e) // FIXME type checking
    | Sif(e, s0, s1) ->
        let (t, e') = inferExpr env e
        Typing.equiv env.ctx t Cbool Ktype
        Sif(inferExpr env e, checkStmt env s0, checkStmt env s1)
    | Swhile(e, s) ->
        let (t, e') = inferExpr env e
        Typing.equiv env.ctx t Cbool Ktype
        Swhile(inferExpr env e, checkStmt env s)
    | Sdecl((i, _) as v, e) ->
        let (t, e') as te' = inferExpr env e
        Env.extendType env.ctx i t
        Sdecl(v, te')
    | Sasgn(e0, e1) ->
        let (t0, e0') = inferExpr env e0
        let (t1, e1') = inferExpr env e1
        Typing.equiv env.ctx t0 t1 Ktype // FIXME type checking
        Sasgn((t0, e0'), (t1, e1'))

and checkStmts (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        let s = checkStmt env hd
        s :: (checkStmts env tl)

and inferFunc (env : Env.env) (v, vcl, cr, s) =
    List.iter (fun (v, dom) -> checkType env Ktype dom) vcl
    checkType env Ktype cr
    List.iter (fun ((id, _), c) -> Env.extendType env.ctx id c) vcl
    let s' = checkStmt env s
    (Carrow(List.map snd vcl, cr), Efunc(v, vcl, cr, s'))

and inferOp (env : Env.env) (o, tel) =
    let tel' = List.map (inferExpr env) tel
    match o with
    | Add -> (Cint, Eop(Add, tel')) // FIXME type checking
    | Cprintf -> (Cunit, Eop(Cprintf, tel')) // FIXME type checking
    | Lt -> (Cbool, Eop(Lt, tel')) // FIXME type checking
    | Multiply -> (Cint, Eop(Multiply, tel')) // FIXME type checking
    | Minus -> (Cint, Eop(Minus, tel')) // FIXME type checking
    | Equal -> (Cbool, Eop(Equal, tel')) // FIXME type checking
    | Idx ->
        match tel' with
        | [ hd; i ] ->
            let (c', e') = hd
            (match Typing.whnf env.ctx c' with
             | Carray c'' -> (c'', Eop(Idx, tel'))
             | _ ->
                 raise (Fatal "TODO inferOp"))
        | _ ->
            raise (Fatal "TODO inferOp")

and inferExpr (env : Env.env) (_, e) =
    match e with
    | Evar(i, _) -> (Env.lookupType env.ctx i, e)
    | Eint i -> (Cint, e)
    | Estring s -> (Cstring, e)
    | Ebool b -> (Cbool, e)
    | Eop(o, tel) -> inferOp env (o, tel)
    | Efunc(v, vcl, cr, s) -> inferFunc env (v, vcl, cr, s)
    | Eapp(f, args) ->
        let (t, f') as tf' = inferExpr env f
        match Typing.whnf env.ctx t with
        | Carrow(dom, cod) ->
            let args' = List.map2 (checkExpr env) args dom
            (cod, Eapp(tf', args'))
        | _ -> raise (TypeError "TODO inferExpr")
    | Etuple tel ->
        let tel' = List.map (inferExpr env) tel
        (Cprod(List.map fst tel'), Etuple tel')
    | Ector((Cstruct(id, _) as t), sel) ->
        match env.struct_def.TryGetValue(id) with
        | false, _ -> raise (TypeError "TODO inferExpr")
        | true, stl ->
            let init_field (name, t) =
                match List.tryFind (fun (s, _) -> s = name) sel with
                | Some(s, e) -> (s, checkExpr env e t)
                | None -> (name, (t, Edefault t))
            (t, Ector(t, List.map init_field stl))
    | Ector _ -> raise (TypeError "TODO inferExpr")
    | Earray tel ->
        match tel with
        | hd :: tl ->
            let (t, e') as te' = inferExpr env hd
            let tl' = List.map (inferExpr env) tl
            List.iter (fun (t', _) -> Typing.equiv env.ctx t t' Ktype) tl'
            (Carray t, Earray(te' :: tl'))
        | _ -> raise (TypeError "TODO inferExpr")
    | Efield(b, (_, Some f)) ->
        let (t, b') as tb' = inferExpr env b
        let lookupField id f =
            match env.struct_def.TryGetValue(id) with
            | false, _ -> raise (TypeError "TODO inferExpr")
            | true, stl ->
                let i = List.findIndex (fun (s, _) -> s = f) stl
                let (_, t) = List.item i stl
                (i, t)
        match Typing.whnf env.ctx t with
        | Cstruct(id, _) ->
            let (i, t) = lookupField id f
            (t, Efield(tb', (i, Some f)))
        | _ -> raise (TypeError "TODO inferExpr")
    | Efield(_, (_, None)) -> raise (Fatal "TODO inferExpr")
    | Edefault ty -> (ty, e)
    // | Eplam(k, t, e') ->
    // let k' = check_kind env k
    // let (c', e'') = inferExpr { env with ctx = Env.extendKind ctx k' } e'
    // (Cforall(k', c'), e'')

and checkExpr (env : Env.env) (t, e) c =
    let (t', _) as te' = inferExpr env (t, e)
    Typing.subType env.ctx t' c
    te'

let scanProg (env : Env.env) = function
    | Sdecl((i, _), (_, Efunc(_, vcl, cr, _))) ->
        List.iter (fun (_, c) -> (checkType env Ktype c)) vcl
        checkType env Ktype cr
        Env.extendType env.ctx i (Carrow(List.map snd vcl, cr))
    | _ -> ()

let rec checkProg (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        let s =
            match hd with
            | Sexpr _ -> checkStmt env hd
            | Sblk _ -> raise (Error "TODO checkProg")
            | Sret _ -> raise (Error "TODO checkProg")
            | Sif _ -> checkStmt env hd
            | Swhile _ -> checkStmt env hd
            | Sdecl(g, (_, Efunc(v, vcl, cr, s))) ->
                Sdecl(g, inferFunc env (v, vcl, cr, s))
            | Sdecl _ -> checkStmt env hd
            | Sasgn _ -> checkStmt env hd
        s :: (checkProg env tl)

let checkModule (env : Env.env) (tt, prog) =
    // TODO add interface and extension
    List.iter (scanHeader env) tt
    List.iter (checkHeader env) tt
    List.iter (scanProg env) prog
    (tt, checkProg env prog)
