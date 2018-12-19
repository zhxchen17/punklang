type mut =
  | Mutable
  | Immutable

type op =
  | Add
  | Cprintf
  | Lt
  | Idx

type kind =
    Ktype
  | Ksing of con
  | Kpi of kind * kind     (* binds *)
  (* | Ksigma of kind * kind  (\* binds *\) *)
  | Kunit

and con =
    Cint
  | Cstring
  | Cbool
  | Cvar of int
  | Cprod of con list * string list option
  | Carrow of con list * con
  | Clam of kind * con     (* binds *)
  | Capp of con * con
  | Cforall of kind * con  (* binds *)
  | Carray of con * expr option
  (* | Cexists of kind * con  (\* binds **\) *)
  | Cref of con
  | Cnamed of Var.id * con
  | Cunit

and iface =
    Iplam of kind * iface * iface (* binds *)
  | Imthds of string * con list * con
  | Ivoid

and expr =
    Evar of Var.id
  | Eint of int
  | Estring of string
  | Ebool of bool
  | Eop of op * expr list
  | Efunc of (Var.id * mut * con) list * con * stmt
  | Eapp of expr * expr list
  | Etuple of con list option * expr list
  | Ector of con * (string * expr) list
  | Econ of con (* for decls only *)
  | Eplam of kind * iface * expr
  | Earray of con * expr list
  | Efield of expr * Var.id
  (* | Eproj of expr * int *)
  (* | Epapp of expr * con *)
  (* | Epack of con * expr * con *)
  (* | Eunpack of variable * expr * expr   (\* binds *\) *)

and stmt =
    Sexpr of expr
  | Sblk of stmt list
  | Sret of expr
  | Sif of expr * stmt * stmt
  | Swhile of expr * stmt
  | Sdecl of Var.id * mut * con * expr
  | Sasgn of expr * expr
