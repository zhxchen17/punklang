open Tir
open Ast
open Equiv
open Utils

let rec check_kind ctx k =
  match k with
  | Tkind_type -> Ktype
  | Tkind_sing c ->
    let c' = check_con ctx c Ktype in
    Ksing c'
  | Tkind_pi (k0, k1) ->
    let k' = check_kind ctx k0 in
    check_kind (Env.extend_kind ctx k') k1
  | Tkind_unit -> Kunit

and infer_con ctx c =
  match c with
  | Tcon_var i ->
    let c' = Cvar i in
    (c', selfify c' (Env.lookup_kind ctx i))
  | Tcon_lam (k, c') ->
    let k' = check_kind ctx k in
    let (c'', k'') = infer_con (Env.extend_kind ctx k') c' in
    (Clam(k', c''), Kpi (k', k''))
  | Tcon_app (c0, c1) ->
    begin match infer_con ctx c0 with
      | (c0', Kpi (dom, cod)) ->
        let c1' = check_con ctx c1 dom in
        (Capp(c0', c1'), Subst.subst_kind c1' cod)
      | _ -> raise (TypeError "infer_con")
    end
  | Tcon_unit -> (Cunit, Kunit)
  | Tcon_arrow (c0, c1) ->
    let c0' = List.map (fun c' -> check_con ctx c' Ktype) c0 in
    let c1' = check_con ctx c1 Ktype in
    let c' = Carrow (c0', c1') in
    (c', Ksing c')
  | Tcon_forall (k, c') ->
    let k' = check_kind ctx k in
    let c'' = check_con (Env.extend_kind ctx k') c' Ktype in
    (c'', Ksing c'')
  | Tcon_prod (cl, s) ->
    let cl' = List.map (fun c' -> check_con ctx c' Ktype) cl in
    let c' = Cprod (cl', s) in
    (c', Ksing c')
  | Tcon_ref c' ->
    let c'' = check_con ctx c' Ktype in
    (Cref c'', Ksing (Cref c''))
  | Tcon_int -> (Cint, Ksing Cint)
  | Tcon_string -> (Cstring, Ksing Cstring)
  | Tcon_bool -> (Cbool, Ksing Cbool)
  | Tcon_named (id, _) ->
    let c' = Env.lookup_type ctx id in
    (c', Ksing c')
  | Tcon_array (c', x) ->
    let c'' = check_con ctx c' Ktype in
    let x' = Option.map x (infer_expr ctx) in
    let ca = Carray (c'', Option.map x' snd) in
    (ca, Ksing ca)

and check_con ctx c k =
  let (c', k') = infer_con ctx c in
  subkind ctx k' k;
  c'

and infer_expr ctx e =
  match e with
  | Texpr_var (id, x) -> (Env.lookup_type ctx id, Evar (id, x))
  | Texpr_func (vmcl, cr, s) ->
    let vmcl' =
      List.map (fun (v, m, dom) ->
          (v, Attrs.translate_attrs m, check_con ctx dom Ktype)) vmcl in
    let cr' = check_con ctx cr Ktype in
    let ctx' = List.fold_left
        (fun c ((id, _), _, ty) -> Env.extend_type c id ty) ctx vmcl' in
    let (c', s') = infer_stmt ctx' s in
    equiv ctx c' cr' Ktype;
    (Carrow ((List.map (fun (_, _, c) -> c) vmcl'), cr'),
     Efunc (vmcl', cr', s'))
  | Texpr_app (e', params) ->
    begin match infer_expr_whnf ctx e' with
      | (Carrow (dom, cod), e'') ->
        let p' = List.map2 (fun d p -> check_expr ctx p d) dom params in
        (cod, Eapp (e'', p'))
      | _ -> raise (TypeError "infer_expr")
    end
  | Texpr_plam (k, t, e') ->
    let k' = check_kind ctx k in
    let (c', e'') = infer_expr (Env.extend_kind ctx k') e' in
    (Cforall (k', c'), e'')
  | Texpr_tuple el ->
    let cel = List.map (infer_expr ctx) el in
    let cl = List.map fst cel in
    (Cprod (cl, None), Etuple cel)
  | Texpr_int i -> (Cint, Eint i)
  | Texpr_string s -> (Cstring, Estring s)
  | Texpr_bool b -> (Cbool, Ebool b)
  | Texpr_con c ->
    let (c', _) = infer_con ctx c in
    (c', Econ c')
  | Texpr_op (o, el) ->
    (* TODO *)
    let cel' = List.map (infer_expr ctx) el in
    begin match o with
      | Top_add ->
        (Cint, Eop (Add, cel'))
      | Top_cprintf ->
        (Cunit, Eop (Cprintf, cel'))
      | Top_lt -> (Cbool, Eop (Lt, cel'))
      | Top_idx ->
        begin match cel' with
          | [hd; i] ->
            let (c', e') = hd in
            begin match c' with
              | Carray (c'', _) -> (c'', Eop (Idx, cel'))
              | _ -> raise (Fatal "indexing from nonarray is not supported yet")
            end
          | _ -> raise (Fatal "indexing operator must have exactly two oprands")
        end
    end
  | Texpr_field (e', (id, Some f)) ->
    assert (id = -1);
    begin match infer_expr ctx e' with
      | (Cnamed (_, Cprod (cl, Some sl)), _) as te' ->
        let rec find x lst =
          match lst with
          | [] -> raise (Error "field name not found")
          | h::t -> if x = h then 0 else 1 + find x t in
        let i = find f sl in
        let c' = List.nth cl i in
        (c', Efield (te', (i, Some f)))
      | (c, _) ->
        raise (Error ("unable to access field " ^ f ^ " " ^ (string_of_con c)))
    end
  | Texpr_field (e', (id, None)) ->
    raise (Fatal "field must have a name to be accessed")
  | Texpr_ctor (Tcon_named ((id, _) as n), sel) ->
    begin match Env.lookup_type ctx id with
      | Cnamed (v, Cprod (cl, Some sl)) as c
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
        let sel' = reorder sl sel in
        let sel'' =
          List.mapi
            (fun i (s, e) ->
               let (c', _) as te' = infer_expr ctx e in
               equiv ctx c' (List.nth cl i) Ktype;
               (s, te')) sel' in
        (c, Ector (c, sel''))
      | _ -> raise (Error "illegal constructor - not found")
    end
  | Texpr_ctor _ -> raise (Fatal "illegal constructor")
  | Texpr_array el ->
    let h = List.hd el in
    let (ca, _) = infer_expr ctx h in
    (Carray (ca, Some (Eint (List.length el))),
     Earray (ca, List.map (fun e' -> check_expr ctx e' ca) el))

and infer_expr_whnf ctx e =
  let (c, _) as te' = infer_expr ctx e in
  (whnf ctx c, te')

and infer_stmt ctx s =
  match s with
  | Tstmt_ret e ->
    let (c, _) as te' = infer_expr ctx e in
    (c, Sret te')
  | Tstmt_blk [] -> (Cunit, Sblk [])
  | Tstmt_blk [s'] ->
    let (c, s'') = infer_stmt ctx s' in
    (c, Sblk [s''])
  | Tstmt_blk (hd::next) ->
    begin match hd with
      | Tstmt_decl ((id, _) as n, _, _, e) ->
        let hd' = check_stmt ctx hd Cunit in
        let (c, _) = infer_expr ctx e (* TODO recursive definition *) in
        let cn = match e with Texpr_con _ -> Cnamed (n, c) | _ -> c in
        begin match infer_stmt (Env.extend_type ctx id cn) (Tstmt_blk next) with
          | (c', Sblk next') -> (c', Sblk (hd'::next'))
          | _ -> raise (Fatal "broken code block in type checking")
        end
      | _ ->
        begin match infer_stmt ctx (Tstmt_blk next) with
          | (c, Sblk next') ->
            let hd' = check_stmt ctx hd c in
            (c, Sblk (hd'::next'))
          | _ -> raise (Fatal "broken code block in type checking")
        end
    end
  | Tstmt_if (e, s0, s1) ->
    let e' = check_expr ctx e Cbool in
    let (c0', s0') = infer_stmt ctx s0 in
    let (c1', s1') = infer_stmt ctx s1 in
    equiv ctx c0' c1' Ktype;
    (c0', Sif (e', s0', s1'))
  | Tstmt_while (e, s') ->
    let e' = check_expr ctx e Cbool in
    let (c, s'') = infer_stmt ctx s' in
    (c, Swhile (e', s''))
  | Tstmt_decl (v, m, Some c, e) ->
    let (c', e') = infer_expr ctx e in
    (* FIXME check c' == c *)
    (Cunit, Sdecl (v, Attrs.translate_attrs m, (c', e')))
  | Tstmt_decl (v, m, None, e) ->
    let (c', e') = infer_expr ctx e in
    (Cunit, Sdecl (v, Attrs.translate_attrs m, (c', e')))
  | Tstmt_asgn (x, e) ->
    (* TODO check x: typeof(e) *)
    let te' = infer_expr ctx e in
    let tx' = infer_expr ctx x in
    (Cunit, Sasgn (tx', te'))
  | Tstmt_expr e ->
    let te' = infer_expr ctx e in
    (Cunit, Sexpr te')

and check_expr ctx e c =
  let (c', _) as te' = infer_expr ctx e in
  equiv ctx c' c Ktype;
  te'

and check_stmt ctx s c =
    match s with
  | Tstmt_ret e ->
    let e' = check_expr ctx e c in
    Sret e'
  | Tstmt_blk [] -> Sblk []
  | Tstmt_blk [s'] ->
    let s'' = check_stmt ctx s' c in
    Sblk [s'']
  | Tstmt_blk sl ->
    let sl' = List.map (fun s -> check_stmt ctx s c) sl in
    Sblk sl'
  | Tstmt_if (e, s0, s1) ->
    let e' = check_expr ctx e Cbool in
    let s0' = check_stmt ctx s0 c in
    let s1' = check_stmt ctx s1 c in
    Sif (e', s0', s1')
  | Tstmt_while (e, s') ->
    let e' = check_expr ctx e Cbool in
    let s'' = check_stmt ctx s' c in
    (Swhile (e', s''))
  | Tstmt_decl (v, m, Some c, e) ->
    let (c', e') = infer_expr ctx e in
    Sdecl (v, Attrs.translate_attrs m, (c', e'))
  | Tstmt_decl (v, m, None, (Texpr_con _ as e)) ->
    let (c', _) = infer_expr ctx e in
    Sdecl (v, Attrs.translate_attrs m, (c', Econ (Cnamed (v, c'))))
  | Tstmt_decl (v, m, None, e) ->
    let (c', e') = infer_expr ctx e in
    Sdecl (v, Attrs.translate_attrs m, (c', e'))
  | Tstmt_asgn (x, e) ->
    (* TODO *)
    let te' = infer_expr ctx e in
    let tx' = infer_expr ctx x in
    Sasgn (tx', te')
  | Tstmt_expr e ->
    let te' = infer_expr ctx e in
    Sexpr te'
