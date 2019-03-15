open Tir
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
  method private extract_id stmt =
    match stmt with
    | Tstmt_decl ((id, Some name), _, _, _) when id >= 0 ->
      env <- Env.add_id env id name
    | Tstmt_decl ((id, _), _, _, _) when id < 0 ->
      raise (Fatal "id is negative")
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
    match Resolve.resolve_stmt env (Tstmt_blk prog) with
    | Tstmt_blk sl -> sl
    | _ -> raise (Fatal "failed to unpack resolved program")
  method elaborate prog =
    match Elaborate.elab_stmt env (Tstmt_blk prog) with
    | Tstmt_blk sl -> sl
    | _ -> raise (Fatal "failed to unpack elaborated program")
  method type_check prog =
    match Check.check_stmt env (Tstmt_blk prog) with
    | Sblk sl -> sl
    | _ -> raise (Fatal "failed to unpack type checked program")
  method analyze prog =
    match Analysis.check_mut_stmt env (Sblk prog) with
    | Sblk sl -> sl
    | _ -> raise (Fatal "failed to unpack analyzed program")
  method emit prog =
    let emitter = Emit.new_emitter () in
    let _ = emitter#emit_stmt env (Sblk prog) in
    emitter#get_module ()
  method llvm_gen mdl =
    Llvm_gen.gen_module mdl
  method compile code =
    code
    |> self#parse
    |> self#resolve
    |> self#elaborate
    |> self#type_check
    |> self#analyze
    |> self#emit
    |> self#llvm_gen
end;;
