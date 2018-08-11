type op =
  | Add

type kind =
    Ktype
  | Ksing of con
  | Kpi of kind * kind     (* binds *)
  | Ksigma of kind * kind  (* binds *)
  | Kunit
and con =
    Cint
  | Cvar of int
  | Cprod of con list * string list option
  | Carrow of con list * con
  | Clam of kind * con     (* binds *)
  (* | Cforall of kind * con  (\* binds *\) *)
  (* | Cexists of kind * con  (\* binds **\) *)
  | Cref of con
  | Cnamed of Var.id * con option
  | Cunit

type tcls =
    Tplam of kind * tcls * tcls (* binds *)
  | Tmthds of string * con list * con
  | Tvoid

type expr =
    Evar of Var.id
  | Eint of int
  | Eop of op * expr list
  | Efunc of (Var.id * con) list * con * stmt
  | Eapp of expr * expr list
  | Etuple of expr list
  | Econ of con (* for decls only *)
  | Eplam of kind * tcls * expr
  (* | Epapp of expr * con *)
  (* | Epack of con * expr * con *)
  (* | Eunpack of variable * expr * expr   (\* binds *\) *)

and stmt =
    Sexpr of expr
  | Sblk of stmt list
  | Sret of expr
  | Sif of expr * stmt * stmt
  | Swhile of expr * stmt
  | Sdecl of Var.id * con option * expr
  | Sasgn of Var.id * expr
