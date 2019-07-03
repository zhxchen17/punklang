module Elaborate

open Tir
open Errors
open ir

let rec elabCon env = function
    | Tcon_prod(cl, _) -> Ir.Cprod(List.map (elabCon env) cl)
    | Tcon_arrow(cpl, cr) ->
        Ir.Carrow(List.map (elabCon env) cpl, elabCon env cr)
    | Tcon_ref c -> Ir.Cref(elabCon env c)
    | Tcon_named v -> Ir.Cstruct v
    | Tcon_app(c0, c1) -> Ir.Capp(elabCon env c0, [ elabCon env c1 ])
    | Tcon_unit -> Ir.Cunit
    | Tcon_int -> Ir.Cint
    | Tcon_string -> Ir.Cstring
    | Tcon_bool -> Ir.Cbool
    | Tcon_var i -> Ir.Cvar i
    | Tcon_array c -> Ir.Carray(elabCon env c)

let rec defType (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        match hd with
        | Tstmt_struct(v, stl) ->
            let sl = List.map fst stl
            let cl = List.map snd stl
            let tyl = List.map (elabCon env) cl
            let def = Ir.Dstruct([], List.zip sl tyl)
            (v, def) :: (defType env tl)
        | _ -> defType env tl

let elabOp = function
    | Top_add -> Ir.Add
    | Top_multiply -> Ir.Multiply
    | Top_minus -> Ir.Minus
    | Top_equal -> Ir.Equal
    | Top_cprintf -> Ir.Cprintf
    | Top_lt -> Ir.Lt
    | Top_idx -> Ir.Idx

let rec elabExpr (env : Env.env) = function
    | Texpr_var v -> (Ir.genSym(), Ir.Evar v)
    | Texpr_int i -> (Ir.Cint, Ir.Eint i)
    | Texpr_string s -> (Ir.Cstring, Ir.Estring s)
    | Texpr_bool b -> (Ir.Cbool, Ir.Ebool b)
    | Texpr_op(o, el) ->
        (Ir.genSym(), Ir.Eop(elabOp o, List.map (elabExpr env) el))
    | Texpr_func(vcl, c, s) ->
        let args = List.map (fun (v, c) -> (v, elabCon env c)) vcl
        let cr = (elabCon env c)
        let body = elabStmt env s
        (Ir.genSym(), Ir.Efunc(Var.newvar None, args, cr, body))
    | Texpr_app(e, el) ->
        (Ir.genSym(), Ir.Eapp(elabExpr env e, List.map (elabExpr env) el))
    | Texpr_tuple el ->
        (Ir.genSym(), Ir.Etuple(List.map (elabExpr env) el))
    | Texpr_ctor(c, sel) ->
        let fl = List.map (fun (s, e) -> (s, elabExpr env e)) sel
        (Ir.genSym(), Ir.Ector(elabCon env c, fl))
    | Texpr_array el ->
        (Ir.genSym(), Ir.Earray(List.map (elabExpr env) el))
    | Texpr_field(e, i) ->
        (Ir.genSym(), Ir.Efield(elabExpr env e, i))

and elabStmt (env : Env.env) = function
    | Tstmt_expr e -> Ir.Sexpr(elabExpr env e)
    | Tstmt_blk sl -> Ir.Sblk(List.map (elabStmt env) sl)
    | Tstmt_ret e -> Ir.Sret(elabExpr env e)
    | Tstmt_if(e, s0, s1) ->
        Ir.Sif(elabExpr env e, elabStmt env s0, elabStmt env s1)
    | Tstmt_while(e, s) ->
        Ir.Swhile(elabExpr env e, elabStmt env s)
    | Tstmt_decl(v, m, c, e) ->
        Ir.Sdecl(v, elabExpr env e)
    | Tstmt_asgn(e0, e1) ->
        Ir.Sasgn(elabExpr env e0, elabExpr env e1)
    | Tstmt_struct(v, stl) ->
        Ir.Sexpr(Ir.Cprod [], Ir.Etuple [])

let rec elabProg (env : Env.env) = function
    | [] -> []
    | hd :: tl ->
        match hd with
        | Tstmt_struct _ ->
            elabProg env tl
        | _ ->
            (elabStmt env hd) :: (elabProg env tl)

let elabModule env prog = (defType env prog, elabProg env prog)
