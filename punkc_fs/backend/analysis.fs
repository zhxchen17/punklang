module Analysis

open ir.Ast
open Errors

let is_lvalue e =
    match e with
    | Evar _ -> true
    | _ -> false

let is_mutable (env : Env.env) e =
    match e with
    | Evar(id, _) -> env.mut_set.ContainsKey(id)
    | _ -> false

let rec check_mut_texp (env : Env.env) (t, e) =
    match e with
    | Efunc(id, vmcl, c, s) ->
        let add_mut (env : Env.env) ((id, _), _) = env.mut_set.Add(id, ())
        List.iter (add_mut env) vmcl
        (t, Efunc(id, vmcl, c, check_mut_stmt env s))
    | _ -> (t, e)

and check_mut_stmt env s =
    match s with
    | Sexpr e -> Sexpr(check_mut_texp env e)
    | Sblk(hd :: next) ->
        (match hd with
         | Sdecl((id, _), Mutable, e) ->
             env.mut_set.Add(id, ())
             ()
         | _ -> ())
        (match check_mut_stmt env (Sblk next) with
         | Sblk sl -> Sblk(hd :: sl)
         | _ -> raise (BackendFatal "mutability check is broken"))
    | Sblk [] -> s
    | Sret e -> Sret(check_mut_texp env e)
    | Sif(e, s0, s1) ->
        Sif(check_mut_texp env e, check_mut_stmt env s0, check_mut_stmt env s1)
    | Swhile(e, s') -> Swhile(check_mut_texp env e, check_mut_stmt env s')
    | Sdecl(v, m, e) -> Sdecl(v, m, check_mut_texp env e)
    | Sasgn((_, e0') as e0, e1) ->
        if is_mutable env e0' then Sasgn(e0, check_mut_texp env e1)
        else raise (BackendError "immutable value cannot be modified")
