open Ast

exception Fatal of string
exception Error of string
exception TypeError of string
exception EquivTypeError of string * string * string
exception SyntaxError of string

let table_size = 42
let buf_size = 17

let rec string_of_con c =
  match c with
  | Cint -> "Cint"
  | Cvar i -> "(Cvar " ^ string_of_int i ^ ")"
  | Cprod (cl, None) ->
    "Cprod [" ^ String.concat ", " (List.map string_of_con cl) ^ "]"
  | Cprod (cl, Some sl) ->
    "Cprod [" ^ String.concat ", " (List.map string_of_con cl) ^ "]s"
  | Carrow (cl , c) ->
    "Carrow ([" ^ (String.concat ", " (List.map string_of_con cl)) ^ "], "
    ^ (string_of_con c) ^ ")"
  | Cref c ->
    "(Cref " ^ string_of_con c ^ ")"
  | Cunit -> "Cunit"
  | Cnamed ((id, _), c) -> "Cnamed (" ^ (string_of_int id) ^ ", "
                           ^ (string_of_con c)  ^ ")"
  | Carray (c, _) -> "(Carray " ^ (string_of_con c) ^ ")"
  | Cstring -> "Cstring"
  | Cbool -> "Cbool"
  | _ -> raise (Fatal "unimplemented constructor")

and string_of_exp e =
  match e with
  | Etuple _ -> "Etuple"
  | Econ c -> "Econ (" ^ (string_of_con c) ^ ")"
  | _ -> "unknown"
