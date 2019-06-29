module Elaborate

open Tir
open Errors
open ir

let rec elab_con env = function
    | Tcon_prod(cl, _) -> Ir.Cprod(List.map (elab_con env) cl)
    | Tcon_arrow(cpl, cr) ->
        Ir.Carrow(List.map (elab_con env) cpl, elab_con env cr)
    | Tcon_ref c -> Ir.Cref(elab_con env c)
    | Tcon_named v -> Ir.Cstruct v
    | Tcon_app(c0, c1) -> Ir.Capp(elab_con env c0, [ elab_con env c1 ])
    | Tcon_unit -> Ir.Cunit
    | Tcon_int -> Ir.Cint
    | Tcon_string -> Ir.Cstring
    | Tcon_bool -> Ir.Cbool
    | Tcon_var i -> Ir.Cvar i
    | Tcon_array c -> Ir.Carray(elab_con env c)

let rec def_type (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        match hd with
        | Tstmt_decl(v, _, _, Texpr_con(Tcon_prod(cl, Some sl))) ->
            let tyl = List.map (elab_con env) cl
            let def = Ir.Dstruct([], List.zip sl tyl)
            (v, def) :: (def_type env tl)
        | _ -> def_type env tl

let elab_op = function
    | Top_add -> Ir.Add
    | Top_multiply -> Ir.Multiply
    | Top_minus -> Ir.Minus
    | Top_equal -> Ir.Equal
    | Top_cprintf -> Ir.Cprintf
    | Top_lt -> Ir.Lt
    | Top_idx -> Ir.Idx

let rec elab_expr (env : Env.env) = function
    | Texpr_var v -> (Ir.gen_sym(), Ir.Evar v)
    | Texpr_int i -> (Ir.Cint, Ir.Eint i)
    | Texpr_string s -> (Ir.Cstring, Ir.Estring s)
    | Texpr_bool b -> (Ir.Cbool, Ir.Ebool b)
    | Texpr_op(o, el) ->
        (Ir.gen_sym(), Ir.Eop(elab_op o, List.map (elab_expr env) el))
    | Texpr_func(vcl, c, s) ->
        let args = List.map (fun (v, c) -> (v, elab_con env c)) vcl
        let cr = (elab_con env c)
        let body = elab_stmt env s
        (Ir.gen_sym(), Ir.Efunc(Var.newvar None, args, cr, body))
    | Texpr_app(e, el) ->
        (Ir.gen_sym(), Ir.Eapp(elab_expr env e, List.map (elab_expr env) el))
    | Texpr_tuple el ->
        (Ir.gen_sym(), Ir.Etuple(List.map (elab_expr env) el))
    | Texpr_ctor(c, sel) ->
        let fl = List.map (fun (s, e) -> (s, elab_expr env e)) sel
        (Ir.gen_sym(), Ir.Ector(elab_con env c, fl))
    | Texpr_con _ -> raise (Fatal "unsupported type expression")
    | Texpr_array el ->
        (Ir.gen_sym(), Ir.Earray(List.map (elab_expr env) el))
    | Texpr_field(e, i) ->
        (Ir.gen_sym(), Ir.Efield(elab_expr env e, i))

and elab_stmt (env : Env.env) = function
    | Tstmt_expr e -> Ir.Sexpr(elab_expr env e)
    | Tstmt_blk sl -> Ir.Sblk(List.map (elab_stmt env) sl)
    | Tstmt_ret e -> Ir.Sret(elab_expr env e)
    | Tstmt_if(e, s0, s1) ->
        Ir.Sif(elab_expr env e, elab_stmt env s0, elab_stmt env s1)
    | Tstmt_while(e, s) ->
        Ir.Swhile(elab_expr env e, elab_stmt env s)
    | Tstmt_decl(v, m, c, e) ->
        Ir.Sdecl(v, elab_expr env e)
    | Tstmt_asgn(e0, e1) ->
        Ir.Sasgn(elab_expr env e0, elab_expr env e1)

let rec elab_prog (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        match hd with
        | Tstmt_decl(v, _, _, Texpr_con(Tcon_prod(cl, Some sl))) ->
            elab_prog env tl
        | _ ->
            (elab_stmt env hd) :: (elab_prog env tl)

let elab_module env prog = (def_type env prog, elab_prog env prog)
