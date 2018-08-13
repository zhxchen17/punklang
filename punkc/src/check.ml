open Ast
open Equiv
open Utils

let rec check_kind ctx k =
  match k with
  | Ktype -> ()
  | Ksing c -> check_con ctx c Ktype
  | Kpi (k0, k1) ->
    check_kind ctx k0;
    check_kind (Env.extend_kind ctx k0) k1
  | Kunit -> ()

and infer_con ctx c =
  match c with
  | Cvar i -> selfify c (Env.lookup_kind ctx i)
  | Clam (k, c') ->
    check_kind ctx k;
    Kpi (k, infer_con (Env.extend_kind ctx k) c')
  | Capp (c0, c1) ->
    begin match infer_con ctx c0 with
      | Kpi (dom, cod) ->
        check_con ctx c1 dom;
        Subst.subst_kind c1 cod
      | _ -> raise (TypeError "infer_con")
    end
  | Cunit -> Kunit
  | Carrow (c0, c1) ->
    List.iter (fun c' -> check_con ctx c' Ktype) c0;
    check_con ctx c1 Ktype;
    Ksing c
  | Cforall (k, c') ->
    check_kind ctx k;
    check_con (Env.extend_kind ctx k) c' Ktype;
    Ksing c
  | Cprod (cl, _) ->
    List.iter (fun c' -> check_con ctx c' Ktype) cl;
    Ksing c
  | Cref c' ->
    check_con ctx c' Ktype;
    Ksing c
  | Cint -> Ksing c
  | Cnamed (v, Some c') -> Ksing c'
  | Cnamed (v, None) -> raise (TypeError "infer_con")
  | Carray (c', _) ->
    check_con ctx c' Ktype;
    Ksing c

and check_con ctx c k = subkind ctx (infer_con ctx c) k

let whnf_annot ctx t =
  check_con ctx t Ktype;
  whnf ctx t

let rec infer_expr ctx e =
  match e with
  | Evar (id, _) -> (Env.lookup_type ctx id, e)
  | Efunc (vcl, cr, s) ->
    List.iter (fun (v, dom) -> check_con ctx dom Ktype) vcl;
    check_con ctx cr Ktype;
    let s' = check_stmt ctx s cr in
    (Carrow ((List.map (fun (_, c) -> c) vcl), cr), Efunc (vcl, cr, s'))
  | Eapp (e', params) ->
    begin match infer_expr_whnf ctx e' with
      | (Carrow (dom, cod), e'') ->
        let p' = List.map2 (fun d p -> check_expr ctx p d) dom params in
        (cod, Eapp (e'', p'))
      | _ -> raise (TypeError "infer_expr")
    end
  | Eplam (k, t, e') ->
    check_kind ctx k;
    let (c', e'') = infer_expr (Env.extend_kind ctx k) e' in
    (Cforall (k, c'), e'')
  | Etuple (_, el) ->
    let cel = List.map (infer_expr ctx) el in
    let cl = List.map fst cel in
    (Cprod (cl, None), Etuple (Some cl, List.map snd cel))
  | Eint _ -> (Cint, e)
  | Econ c -> (c, e)
  | Eop (o, el) -> (Cint, e) (* TODO *)
  | Ector (Cnamed ((id, _) as n, _), sel) ->
    begin match Env.lookup_type ctx id with
      | Cnamed (v, Some (Cprod (cl, Some sl))) as c
        when n = v && List.compare_lengths sl sel = 0 ->
        let rec reorder sl sel =
          let rec remove s sel =
            match sel with
            | ((s', _) as hd)::next ->
              if s' = s then (hd, next)
              else let i, tl = remove s next in (i, hd::tl)
            | [] -> raise (Error ("missing field " ^ s)) in
          match sl with
          | s'::next ->
            let i, tl = remove s' sel in i::(reorder next tl)
          | [] -> []
        in
        (c, Ector (c, reorder sl sel))
      | _ -> raise (Error "illegal constructor")
    end
  | Ector _ -> raise (Fatal "illegal constructor")
  | Earray (_, el) ->
    let h = List.hd el in
    let (ca, _) = infer_expr ctx h in
    (Carray (ca, Some (Eint (List.length el))),
     Earray (Some ca, List.map (fun e' -> check_expr ctx e' ca) el))

and infer_expr_whnf ctx e =
  let (c, e') = infer_expr ctx e in
  (whnf ctx c, e')

and infer_stmt ctx s =
  match s with
  | Sret e ->
    let (c, e') = infer_expr ctx e in
    (c, Sret e')
  | Sblk [] -> (Cunit, s)
  | Sblk [s'] ->
    let (c, s'') = infer_stmt ctx s' in
    (c, Sblk [s''])
  | Sblk (hd::next) ->
    begin match hd with
      | Sdecl ((id, _), _, e) ->
        let hd' = check_stmt ctx hd Cunit in
        let (c, _) = infer_expr ctx e (* TODO recursive definition *) in
        begin match infer_stmt (Env.extend_type ctx id c) (Sblk next) with
          | (c', Sblk next') -> (c', Sblk (hd'::next'))
          | _ -> raise (Fatal "broken code block in type checking")
        end
      | _ ->
        begin match infer_stmt ctx (Sblk next) with
          | (c, Sblk next') ->
            let hd' = check_stmt ctx hd c in
            (c, Sblk (hd'::next'))
          | _ -> raise (Fatal "broken code block in type checking")
        end
    end
  | Sif (e, s0, s1) ->
    let e' = check_expr ctx e Cint in
    let (c0', s0') = infer_stmt ctx s0 in
    let (c1', s1') = infer_stmt ctx s1 in
    equiv ctx c0' c1' Ktype;
    (c0', Sif (e', s0', s1'))
  | Swhile (e, s') ->
    let e' = check_expr ctx e Cint in
    let (c, s'') = infer_stmt ctx s' in
    (c, Swhile (e', s''))
  | Sdecl (v, Some c, e) ->
    let e' = check_expr ctx e c in
    (Cunit, Sdecl (v, Some c, e'))
  | Sdecl (v, None, e) ->
    let (_, e') = infer_expr ctx e in
    (Cunit, Sdecl (v, None, e'))
  | Sasgn (x, e) ->
    (* TODO *)
    let (_, e') = infer_expr ctx e in
    (Cunit, Sasgn (x, e'))
  | Sexpr e ->
    let (_, e') = infer_expr ctx e in
    (Cunit, Sexpr e')

and check_expr ctx e c =
  let (c', e') = infer_expr ctx e in
  equiv ctx c' c Ktype;
  e'

and check_stmt ctx s c =
    match s with
  | Sret e ->
    let e' = check_expr ctx e c in
    Sret e'
  | Sblk [] -> s
  | Sblk [s'] ->
    let s'' = check_stmt ctx s' c in
    Sblk [s'']
  | Sblk sl ->
    let sl' = List.map (fun s -> check_stmt ctx s c) sl in
    Sblk sl'
  | Sif (e, s0, s1) ->
    let e' = check_expr ctx e Cint in
    let s0' = check_stmt ctx s0 c in
    let s1' = check_stmt ctx s1 c in
    Sif (e', s0', s1')
  | Swhile (e, s') ->
    let e' = check_expr ctx e Cint in
    let s'' = check_stmt ctx s' c in
    (Swhile (e', s''))
  | Sdecl (v, Some c, e) ->
    let e' = check_expr ctx e c in
    Sdecl (v, Some c, e')
  | Sdecl (v, None, e) ->
    let (_, e') = infer_expr ctx e in
    Sdecl (v, None, e')
  | Sasgn (x, e) ->
    (* TODO *)
    let (_, e') = infer_expr ctx e in
    Sasgn (x, e')
  | Sexpr e ->
    let (_, e') = infer_expr ctx e in
    Sexpr e'
