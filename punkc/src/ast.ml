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
  | Ksing of ty
  | Kpi of kind * kind     (* binds *)
  (* | Ksigma of kind * kind  (\* binds *\) *)
  | Kunit

and ty =
    Cint
  | Cstring
  | Cbool
  | Cvar of int
  | Cprod of ty list * string list option
  | Carrow of ty list * ty
  | Clam of kind * ty     (* binds *)
  | Capp of ty * ty
  | Cforall of kind * ty  (* binds *)
  | Carray of ty * exp option
  (* | Cexists of kind * con  (\* binds **\) *)
  | Cref of ty
  | Cnamed of Var.id * ty
  | Cunit

and iface =
    Iplam of kind * iface * iface (* binds *)
  | Imthds of string * ty list * ty
  | Ivoid

and exp =
    Evar of Var.id
  | Eint of int
  | Estring of string
  | Ebool of bool
  | Eop of op * exp list
  | Efunc of (Var.id * mut * ty) list * ty * stmt
  | Eapp of exp * exp list
  | Etuple of ty list option * exp list
  | Ector of ty * (string * exp) list
  | Econ of ty (* for decls only *)
  | Eplam of kind * iface * exp
  | Earray of ty * exp list
  | Efield of exp * Var.id
  (* | Eproj of expr * int *)
  (* | Epapp of expr * con *)
  (* | Epack of con * expr * con *)
  (* | Eunpack of variable * expr * expr   (\* binds *\) *)

and texp = ty * exp

and stmt =
    Sexpr of exp
  | Sblk of stmt list
  | Sret of exp
  | Sif of exp * stmt * stmt
  | Swhile of exp * stmt
  | Sdecl of Var.id * mut * ty * exp
  | Sasgn of exp * exp
