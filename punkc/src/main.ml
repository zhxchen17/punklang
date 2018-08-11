open Ast

(* Parse a string into an ast *)
let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let parse_expr s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.term Lexer.read lexbuf in
  ast

exception Fatal of string
exception Error of string

module Option = Core.Option

let rec resolve_con env con =
  match con with
  | Cprod (cl, ll) -> Cprod (List.map (resolve_con env) cl, ll)
  | Carrow (cpl, cr) -> Carrow (List.map (resolve_con env) cpl, resolve_con env cr)
  | Clam (k, c) -> Clam (resolve_kind env k, resolve_con env c)
  | Cref c -> Cref (resolve_con env c)
  | Cnamed ((-1, Some x), cref) ->
    begin match Env.find_id_opt env x with
    | Some id -> Cnamed ((id, Some x), cref)
    | None -> raise (Error "undeclared type name")
    end
  | Cnamed ((_, Some x), _) -> raise (Fatal "type id is negative")
  | _ -> con
and resolve_kind env kind =
  match kind with
  | Ksing c -> Ksing (resolve_con env c)
  | Kpi (k0, k1) -> Kpi (resolve_kind env k0, resolve_kind env k1)
  | Ksigma (k0, k1) -> Ksigma (resolve_kind env k1, resolve_kind env k1)
  | _ -> kind
and resolve_tcls env tcls =
  match tcls with
  | Tplam (k, t0, t1) ->
    Tplam (resolve_kind env k, resolve_tcls env t0, resolve_tcls env t1)
  | Tmthds (s, cpl, cr) ->
    Tmthds (s, List.map (resolve_con env) cpl, resolve_con env cr)
  | Tvoid -> Tvoid

let rec resolve_expr env expr =
  match expr with
  | Evar (-1, Some x) -> Evar (Env.StringMap.find x env.Env.var_id_map, Some x)
  | Evar (_, Some x) -> raise (Fatal "id is negative")
  | Eop (o, el) -> Eop (o, List.map (resolve_expr env) el)
  | Efunc (params, ret, s) ->
    let update_id env ((id, s), _) =
      Option.value_map s ~default:env ~f:(Env.add_id env id) in
    let env' = List.fold_left update_id env params in
    Efunc (List.map (fun (x, c) -> (x, resolve_con env c)) params,
           resolve_con env ret,
           resolve_stmt env' s)
  | Etuple el -> Etuple (List.map (resolve_expr env) el)
  | Econ c -> Econ (resolve_con env c)
  | Eplam (k, t, e) ->
    Eplam (resolve_kind env k, resolve_tcls env t, resolve_expr env e)
  | Eapp (e, params) ->
    Eapp (resolve_expr env e, List.map (resolve_expr env) params)
  | _ -> expr
and resolve_stmt env stmt =
  match stmt with
  | Sexpr e -> Sexpr (resolve_expr env e)
  | Sblk sl ->
    let update_id (env, sl) s =
      match s with
      | Sdecl ((id, Some x), _, e) when id >= 0 ->
        (Env.add_id env id x, sl @ [resolve_stmt env s])
      | Sdecl ((id, _), _, _) when id < 0 -> raise (Fatal "id is negative")
      | _ -> (env, sl @ [resolve_stmt env s]) in
    let _, sl' = List.fold_left update_id (env, []) sl in
    Sblk sl'
  | Sret e -> Sret (resolve_expr env e)
  | Sif (e, s0, s1) ->
    Sif (resolve_expr env e, resolve_stmt env s0, resolve_stmt env s1)
  | Swhile (e, s) -> Swhile (resolve_expr env e, resolve_stmt env s)
  | Sdecl (v, Some c, e) ->
    Sdecl (v, Some (resolve_con env c), resolve_expr env e)
  | Sdecl (v, None, e) -> Sdecl (v, None, resolve_expr env e)
  | Sasgn (v, e) -> Sasgn (v, resolve_expr env e)

(* let rec emit_expr env expr =
 *   match expr with
 *   | Evar (-1, Some x) -> raise (Fatal "unresolved variable")
 *   | Evar (id, Some x) -> raise (Fatal "id is negative")
 *   | Eop (o, el) -> Eop (o, List.map (resolve_expr env) el)
 *   | Efunc (params, ret, s) ->
 *     let update_id env ((id, s), _) =
 *       let env = Env.add_param env id in
 *       Option.value_map s ~default:env ~f:(Env.add_id env id) in
 *     let env' = List.fold_left update_id env params in
 *     Efunc (List.map (fun (x, c) -> (x, resolve_con env c)) params,
 *            resolve_con env ret,
 *            resolve_stmt env' s)
 *   | Etuple el -> Etuple (List.map (resolve_expr env) el)
 *   | Econ c -> Econ (resolve_con env c)
 *   | Eplam (k, t, e) ->
 *     Eplam (resolve_kind env k, resolve_tcls env t, resolve_expr env e)
 *   | Eapp (e, params) ->
 *     Eapp (resolve_expr env e, List.map (resolve_expr env) params)
 *   | _ -> expr
 * and emit_stmt env stmt =
 *   match stmt with
 *   | Sexpr e -> Sexpr (resolve_expr env e)
 *   | Sblk sl ->
 *     let update_id (env, sl) s =
 *       match s with
 *       | Sdecl ((id, Some x), _, e) when id >= 0 ->
 *         (Env.add_id env id x, sl @ [resolve_stmt env s])
 *       | Sdecl ((id, _), _, _) when id < 0 -> raise (Fatal "id is negative")
 *       | _ -> (env, sl @ [resolve_stmt env s]) in
 *     let _, sl' = List.fold_left update_id (env, []) sl in
 *     Sblk sl'
 *   | Sret e -> Sret (resolve_expr env e)
 *   | Sif (e, s0, s1) ->
 *     Sif (resolve_expr env e, resolve_stmt env s0, resolve_stmt env s1)
 *   | Swhile (e, s) -> Swhile (resolve_expr env e, resolve_stmt env s)
 *   | Sdecl (v, Some c, e) ->
 *     Sdecl (v, Some (resolve_con env c), resolve_expr env e)
 *   | Sdecl (v, None, e) -> Sdecl (v, None, resolve_expr env e)
 *   | Sasgn (v, e) -> Sasgn (v, resolve_expr env e) *)

class package = object (self)
  val mutable env = Env.new_env ()
  val mutable prog: stmt list = []
  val mutable mdl = ()
  method private extract_id stmt =
    match stmt with
    | Sdecl ((id, Some name), _, _) when id >= 0 ->
      env <- Env.add_id env id name
    | Sdecl ((id, _), _, _) when id < 0 -> raise (Fatal "id is negative")
    | _ -> ()
  method print_defs () =
    Env.StringMap.iter
      (fun k v -> print_string (k ^ " -> " ^ string_of_int v ^ "\n"))
      env.var_id_map;
  method parse s =
    let stmt_list = parse s in
    List.iter self#extract_id stmt_list;
    stmt_list
  method resolve prog =
    match resolve_stmt env (Sblk prog) with
    | Sblk sl -> sl
    | _ -> raise (Fatal "failed to unpack resolved program")
  method emit () = ()
end;;
