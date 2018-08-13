open Ast
open Utils
open Llvm

(* Parse a string into an ast *)
let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let parse_expr s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.term Lexer.read lexbuf in
  ast

class package = object (self)
  val mutable env = Env.empty_env ()
  val mutable prog: stmt list = []
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
    match Resolve.resolve_stmt env (Sblk prog) with
    | Sblk sl -> sl
    | _ -> raise (Fatal "failed to unpack resolved program")
  method type_check prog =
    match Check.infer_stmt env.ctx (Sblk prog) with
    | (Cunit, Sblk sl) -> sl
    | _ -> raise (Fatal "failed to unpack checked program")
  method emit prog =
    let emitter = Emit.new_emitter () in
    let _ = emitter#emit_stmt env (Sblk prog) in
    emitter#get_module ()
  method compile code =
    code
    |> self#parse
    |> self#resolve
    |> self#type_check
    |> self#emit
end;;
