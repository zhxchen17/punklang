module Analysis

module Hashtbl = FSharp.Compatibility.OCaml.Hashtbl

open ir.Ast
open Errors

let is_lvalue e =
    match e with
    | Evar _ -> true
    | _ -> false

let is_mutable (env : Env.env) e =
    match e with
    | Evar(id, _) -> Hashtbl.mem env.mut_set id
    | _ -> false

let rec check_mut_texp (env : Env.env) (t, e) =
    match e with
    | Efunc(vmcl, c, s) ->
        let add_mut (env : Env.env) ((id, _), m, _) =
            match m with
            | Mutable -> Hashtbl.add env.mut_set id ()
            | Immutable -> ()
        List.iter (add_mut env) vmcl
        (t, Efunc(vmcl, c, check_mut_stmt env s))
    | _ -> (t, e)

and check_mut_stmt env s =
    match s with
    | Sexpr e -> Sexpr(check_mut_texp env e)
    | Sblk(hd :: next) ->
        (match hd with
         | Sdecl((id, _), Mutable, e) ->
             Hashtbl.add env.mut_set id ()
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
