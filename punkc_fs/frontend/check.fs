module Check

open ir.Ir
open Errors

let rec infer_type (env : Env.env) = function
    | Cint -> Ktype
    | Cstring -> Ktype
    | Cbool -> Ktype
    | Cvar i ->
        if i >= env.ctx.ksize then
            raise (Fatal "TODO infer_type")
        else
            Ktype
    | Cprod cl ->
        List.iter (check_type env Ktype) cl
        Ktype
    | Carrow(cl, c) ->
        List.iter (check_type env Ktype) cl
        check_type env Ktype c
        Ktype
    | Clam(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extend_kind c Ktype) env.ctx il
        let k = infer_type { env with ctx = ctx' } c
        let kl = List.init (List.length il) (fun _ -> Ktype)
        Kpi(kl, k)
    | Capp(c, cl) ->
        let k = infer_type env c
        match k with
        | Kpi(l, r) ->
            List.iter2 (check_type env) l cl
            r
        | _ -> raise (TypeError "TODO infer_type")
    | Cforall(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extend_kind c Ktype) env.ctx il
        infer_type { env with ctx = ctx' } c
    | Carray c ->
        infer_type env c
    | Cref c ->
        infer_type env c
    | Cstruct(i, _) ->
        match env.ctx.struct_map.TryGetValue(i) with
        | false, _ -> raise (Fatal "TODO infer_type")
        | true, k -> k
    | Cunit ->
        Ktype
    | Csym _ ->
        raise (Fatal "TODO infer_type")
    | Cexists(il, c) ->
        let ctx' = List.fold (fun c _ -> Env.extend_kind c Ktype) env.ctx il
        infer_type { env with ctx = ctx' } c

and check_type (env : Env.env) k c =
    let k' = infer_type env c
    Typing.subkind env.ctx k' k

let scan_header (env : Env.env) ((i, _), d) =
    match d with
    | Dstruct([], _) ->
        env.ctx.struct_map.Add(i, Ktype)
    | Dstruct(il, _) ->
        let len = List.length il
        env.ctx.struct_map.Add(i, Kpi(List.init len (fun _ -> Ktype), Ktype))
    | Diface _ -> raise (Fatal "TODO scan_header")
    | Dalias _ -> raise (Fatal "TODO scan_header")

let check_header (env : Env.env) ((i, _), d) =
    match d with
    | Dstruct(_, stl) ->
        List.iter (fun (_, t) -> check_type env Ktype t) stl
        env.struct_def.Add(i, stl)
    | Diface _ -> raise (Fatal "TODO check_header")
    | Dalias _ -> raise (Fatal "TODO check_header")

let rec check_stmt (env : Env.env) = function
    | Sexpr e ->
        Sexpr(infer_expr env e)
    | Sblk sl ->
        Sblk(check_stmts env sl)
    | Sret e ->
        Sret(infer_expr env e) // FIXME type checking
    | Sif(e, s0, s1) ->
        let (t, e') = infer_expr env e
        Typing.equiv env.ctx t Cbool Ktype
        Sif(infer_expr env e, check_stmt env s0, check_stmt env s1)
    | Swhile(e, s) ->
        let (t, e') = infer_expr env e
        Typing.equiv env.ctx t Cbool Ktype
        Swhile(infer_expr env e, check_stmt env s)
    | Sdecl((i, _) as v, e) ->
        let (t, e') as te' = infer_expr env e
        Env.extend_type env.ctx i t
        Sdecl(v, te')
    | Sasgn(e0, e1) ->
        let (t0, e0') = infer_expr env e0
        let (t1, e1') = infer_expr env e1
        Typing.equiv env.ctx t0 t1 Ktype // FIXME type checking
        Sasgn((t0, e0'), (t1, e1'))

and check_stmts (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        let s = check_stmt env hd
        s :: (check_stmts env tl)

and infer_func (env : Env.env) (v, vcl, cr, s) =
    List.iter (fun (v, dom) -> check_type env Ktype dom) vcl
    check_type env Ktype cr
    List.iter (fun ((id, _), c) -> Env.extend_type env.ctx id c) vcl
    let s' = check_stmt env s
    (Carrow(List.map snd vcl, cr), Efunc(v, vcl, cr, s'))

and infer_op (env : Env.env) (o, tel) =
    let tel' = List.map (infer_expr env) tel
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
                 raise (Fatal "TODO infer_op"))
        | _ ->
            raise (Fatal "TODO infer_op")

and infer_expr (env : Env.env) (_, e) =
    match e with
    | Evar(i, _) -> (Env.lookup_type env.ctx i, e)
    | Eint i -> (Cint, e)
    | Estring s -> (Cstring, e)
    | Ebool b -> (Cbool, e)
    | Eop(o, tel) -> infer_op env (o, tel)
    | Efunc(v, vcl, cr, s) -> infer_func env (v, vcl, cr, s)
    | Eapp(f, args) ->
        let (t, f') as tf' = infer_expr env f
        match Typing.whnf env.ctx t with
        | Carrow(dom, cod) ->
            let args' = List.map2 (check_expr env) args dom
            (cod, Eapp(tf', args'))
        | _ -> raise (TypeError "TODO infer_expr")
    | Etuple tel ->
        let tel' = List.map (infer_expr env) tel
        (Cprod(List.map fst tel'), Etuple tel')
    | Ector((Cstruct(id, _) as t), sel) ->
        match env.struct_def.TryGetValue(id) with
        | false, _ -> raise (TypeError "TODO infer_expr")
        | true, stl ->
            let init_field (name, t) =
                match List.tryFind (fun (s, _) -> s = name) sel with
                | Some(s, e) -> (s, check_expr env e t)
                | None -> (name, (t, Edefault t))
            (t, Ector(t, List.map init_field stl))
    | Ector _ -> raise (TypeError "TODO infer_expr")
    | Earray tel ->
        match tel with
        | hd :: tl ->
            let (t, e') as te' = infer_expr env hd
            let tl' = List.map (infer_expr env) tl
            List.iter (fun (t', _) -> Typing.equiv env.ctx t t' Ktype) tl'
            (Carray t, Earray(te' :: tl'))
        | _ -> raise (TypeError "TODO infer_expr")
    | Efield(b, (_, Some f)) ->
        let (t, b') as tb' = infer_expr env b
        let lookup_field id f =
            match env.struct_def.TryGetValue(id) with
            | false, _ -> raise (TypeError "TODO infer_expr")
            | true, stl ->
                let i = List.findIndex (fun (s, _) -> s = f) stl
                let (_, t) = List.item i stl
                (i, t)
        match Typing.whnf env.ctx t with
        | Cstruct(id, _) ->
            let (i, t) = lookup_field id f
            (t, Efield(tb', (i, Some f)))
        | _ -> raise (TypeError "TODO infer_expr")
    | Efield(_, (_, None)) -> raise (Fatal "TODO infer_expr")
    | Edefault ty -> (ty, e)
    // | Eplam(k, t, e') ->
    // let k' = check_kind env k
    // let (c', e'') = infer_expr { env with ctx = Env.extend_kind ctx k' } e'
    // (Cforall(k', c'), e'')

and check_expr (env : Env.env) (t, e) c =
    let (t', _) as te' = infer_expr env (t, e)
    Typing.subtype env.ctx t' c
    te'

let scan_prog (env : Env.env) = function
    | Sdecl((i, _), (_, Efunc(_, vcl, cr, _))) ->
        List.iter (fun (_, c) -> (check_type env Ktype c)) vcl
        check_type env Ktype cr
        Env.extend_type env.ctx i (Carrow(List.map snd vcl, cr))
    | _ -> ()

let rec check_prog (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        let s =
            match hd with
            | Sexpr _ -> check_stmt env hd
            | Sblk _ -> raise (Error "TODO check_prog")
            | Sret _ -> raise (Error "TODO check_prog")
            | Sif _ -> check_stmt env hd
            | Swhile _ -> check_stmt env hd
            | Sdecl(g, (_, Efunc(v, vcl, cr, s))) ->
                Sdecl(g, infer_func env (v, vcl, cr, s))
            | Sdecl _ -> check_stmt env hd
            | Sasgn _ -> check_stmt env hd
        s :: (check_prog env tl)

let check_module (env : Env.env) (tt, prog) =
    // TODO add interface and extension
    List.iter (scan_header env) tt
    List.iter (check_header env) tt
    List.iter (scan_prog env) prog
    (tt, check_prog env prog)
