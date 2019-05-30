module Check

open Tir
open ir.Ast
open Equiv
open Errors

let rec check_kind (env : Env.env) k =
    let ctx = env.ctx
    match k with
    | Tkind_type -> Ktype
    | Tkind_sing c ->
        let c' = check_con env c Ktype
        Ksing c'
    | Tkind_pi(k0, k1) ->
        let k' = check_kind env k0
        check_kind { env with ctx = Env.extend_kind ctx k' } k1
    | Tkind_unit -> Kunit

and infer_con (env : Env.env) c =
    let ctx = env.ctx
    match c with
    | Tcon_var i ->
        let c' = Cvar i
        (c', selfify c' (Env.lookup_kind ctx i))
    | Tcon_lam(k, c') ->
        let k' = check_kind env k
        let (c'', k'') = infer_con { env with ctx = Env.extend_kind ctx k' } c'
        (Clam(k', c''), Kpi(k', k''))
    | Tcon_app(c0, c1) ->
        (match infer_con env c0 with
         | (c0', Kpi(dom, cod)) ->
             let c1' = check_con env c1 dom
             (Capp(c0', c1'), Subst.subst_kind c1' cod)
         | _ -> raise (TypeError "infer_con"))
    | Tcon_unit -> (Cunit, Kunit)
    | Tcon_arrow(c0, c1) ->
        let c0' = List.map (fun c' -> check_con env c' Ktype) c0
        let c1' = check_con env c1 Ktype
        let c' = Carrow(c0', c1')
        (c', Ksing c')
    | Tcon_forall(k, c') ->
        let k' = check_kind env k
        let c'' = check_con { env with ctx = Env.extend_kind ctx k' } c' Ktype
        (c'', Ksing c'')
    | Tcon_prod(cl, s) ->
        let cl' = List.map (fun c' -> check_con env c' Ktype) cl
        let c' = Cprod(cl', s)
        (c', Ksing c')
    | Tcon_ref c' ->
        let c'' = check_con env c' Ktype
        (Cref c'', Ksing(Cref c''))
    | Tcon_int -> (Cint, Ksing Cint)
    | Tcon_string -> (Cstring, Ksing Cstring)
    | Tcon_bool -> (Cbool, Ksing Cbool)
    | Tcon_named(id, _) ->
        let c' = Env.lookup_type ctx id
        (c', Ksing c')
    | Tcon_array c' ->
        let c'' = check_con env c' Ktype
        let ca = Carray c''
        (ca, Ksing ca)

and check_con (env : Env.env) c k =
    let ctx = env.ctx
    let (c', k') = infer_con env c
    subkind ctx k' k
    c'

and infer_expr (env : Env.env) e =
    let ctx = env.ctx
    match e with
    | Texpr_var(id, x) -> (Env.lookup_type ctx id, Evar(id, x))
    | Texpr_func(vmcl, cr, s) ->
        let vmcl' =
            List.map
                (fun (v, m, dom) ->
                (v, Attrs.translate_attrs m, check_con env dom Ktype)) vmcl
        let cr' = check_con env cr Ktype
        let cf = Carrow((List.map (fun (_, _, c) -> c) vmcl'), cr')
        let roll = (fun c ((id, _), _, ty) -> Env.extend_type c id ty)
        let ctx' = List.fold roll ctx vmcl'
        let s' = check_stmt { env with ctx = ctx' } s
        ((* equiv ctx c' cr' Ktype; *)
         cf, Efunc(vmcl', cr', s'))
    | Texpr_app(e', ``params``) ->
        (match infer_expr_whnf env e' with
         | (Carrow(dom, cod), e'') ->
             let p' = List.map2 (fun d p -> check_expr env p d) dom ``params``
             (cod, Eapp(e'', p'))
         | _ -> raise (TypeError "infer_expr"))
    | Texpr_plam(k, t, e') ->
        let k' = check_kind env k
        let (c', e'') = infer_expr { env with ctx = Env.extend_kind ctx k' } e'
        (Cforall(k', c'), e'')
    | Texpr_tuple el ->
        let cel = List.map (infer_expr env) el
        let cl = List.map fst cel
        (Cprod(cl, None), Etuple cel)
    | Texpr_int i -> (Cint, Eint i)
    | Texpr_string s -> (Cstring, Estring s)
    | Texpr_bool b -> (Cbool, Ebool b)
    | Texpr_con c ->
        let (c', _) = infer_con env c
        (c', Econ c')
    | Texpr_op(o, el) ->
        (* TODO *)
        let cel' = List.map (infer_expr env) el
        (match o with
         | Top_add -> (Cint, Eop(Add, cel'))
         | Top_cprintf -> (Cunit, Eop(Cprintf, cel'))
         | Top_lt -> (Cbool, Eop(Lt, cel'))
         | Top_multiply -> (Cint, Eop(Multiply, cel'))
         | Top_minus -> (Cint, Eop(Minus, cel'))
         | Top_equal -> (Cbool, Eop(Equal, cel'))
         | Top_idx ->
             (match cel' with
              | [ hd; i ] ->
                  let (c', e') = hd
                  (match c' with
                   | Carray c'' -> (c'', Eop(Idx, cel'))
                   | _ ->
                       raise
                           (Fatal "indexing from nonarray is not supported yet"))
              | _ ->
                  raise
                      (Fatal "indexing operator must have exactly two oprands")))
    | Texpr_field(e', (id, Some f)) ->
        assert (id = -1)
        (match infer_expr env e' with
         | (Cnamed(_, Cprod(cl, Some sl)), _) as te' ->
             let rec find x lst =
                 match lst with
                 | [] -> raise (Error "field name not found")
                 | h :: t ->
                     if x = h then 0
                     else 1 + find x t

             let i = find f sl
             let c' = List.nth cl i
             (c', Efield(te', (i, Some f)))
         | (c, _) ->
             raise (Error("unable to access field " ^ f ^ " " ^ (string c))))
    | Texpr_field(e', (id, None)) ->
        raise (Fatal "field must have a name to be accessed")
    | Texpr_ctor(Tcon_named((id, _) as n), sel) ->
        (match Env.lookup_type ctx id with
         | Cnamed(v, Cprod(cl, Some sl)) as c when n = v
                                                   && List.length sl = List.length
                                                                           sel ->
             let rec reorder sl sel =
                 let rec remove s sel =
                     match sel with
                     | ((s', _) as hd) :: next ->
                         if s' = s then (hd, next)
                         else
                             let i, tl = remove s next in (i, hd :: tl)
                     | [] -> raise (Error("missing field " ^ s))
                 match sl with
                 | s' :: next ->
                     let i, tl = remove s' sel in i :: (reorder next tl)
                 | [] -> []

             let sel' = reorder sl sel

             let sel'' =
                 List.mapi (fun i (s, e) ->
                     let (c', _) as te' = infer_expr env e
                     equiv ctx c' (List.nth cl i) Ktype
                     (s, te')) sel'
             (c, Ector(c, sel''))
         | _ -> raise (Error "illegal constructor - not found"))
    | Texpr_ctor _ -> raise (Fatal "illegal constructor")
    | Texpr_array el ->
        let h = List.head el
        let (ca, _) = infer_expr env h
        (Carray ca, Earray(ca, List.map (fun e' -> check_expr env e' ca) el))

and infer_expr_whnf (env : Env.env) e =
    let ctx = env.ctx
    let (c, _) as te' = infer_expr env e
    (whnf ctx c, te')

and check_stmt env s =
    match s with
    | Tstmt_ret e ->
        let (c, _) as te' = infer_expr env e
        Sret te'
    | Tstmt_blk sl ->
        let update_env (env : Env.env) s =
            let ctx = env.ctx
            match s with
            | Tstmt_decl((id, _) as n, _, _, (Texpr_con _ as e)) ->
                let (c', _) = infer_expr env e
                { env with ctx = Env.extend_type ctx id (Cnamed(n, c')) }
            | Tstmt_decl((id, _), _, Some c, e) ->
                let (c', _) = infer_con env c
                { env with ctx = Env.extend_type ctx id c' }
            | Tstmt_decl((id, _), _, None, e) ->
                let (c', _) = infer_expr env e
                { env with ctx = Env.extend_type ctx id c' }
            | _ -> env

        let update_stmt (env : Env.env) s =
            let ctx = env.ctx
            match s with
            | Tstmt_decl((id, _) as n, m, _, Texpr_con _) ->
                let c' = Env.lookup_type ctx id
                Sdecl(n, Attrs.translate_attrs m, (c', Econ c'))
            | Tstmt_decl((id, _) as v, m, Some c, e) ->
                let (c', e') = infer_expr env e
                equiv ctx c' (Env.lookup_type ctx id) Kunit
                Sdecl(v, Attrs.translate_attrs m, (c', e'))
            | Tstmt_decl((id, _) as v, m, None, e) ->
                let (c', e') = infer_expr env e
                Sdecl(v, Attrs.translate_attrs m, (c', e'))
            | _ -> check_stmt env s

        Sblk(Visitors.visit_block env update_env update_stmt sl)
    | Tstmt_if(e, s0, s1) ->
        let e' = check_expr env e Cbool
        let s0' = check_stmt env s0
        let s1' = check_stmt env s1
        Sif(e', s0', s1')
    | Tstmt_while(e, s') ->
        let e' = check_expr env e Cbool
        let s'' = check_stmt env s'
        Swhile(e', s'')
    | Tstmt_decl(v, m, Some c, e) ->
        let (c', e') = infer_expr env e
        (* FIXME check c' == c *)
        Sdecl(v, Attrs.translate_attrs m, (c', e'))
    | Tstmt_decl(v, m, None, e) ->
        let (c', e') = infer_expr env e
        Sdecl(v, Attrs.translate_attrs m, (c', e'))
    | Tstmt_asgn(x, e) ->
        (* TODO check x: typeof(e) *)
        let te' = infer_expr env e
        let tx' = infer_expr env x
        Sasgn(tx', te')
    | Tstmt_expr e ->
        let te' = infer_expr env e
        Sexpr te'

and check_expr (env : Env.env) e c =
    let ctx = env.ctx
    let (c', _) as te' = infer_expr env e
    equiv ctx c' c Ktype
    te'
