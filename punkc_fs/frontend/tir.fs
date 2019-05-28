module Tir

type mut =
  | Tmut
  | Timm

type op =
  | Top_add
  | Top_multiply
  | Top_minus
  | Top_equal
  | Top_cprintf
  | Top_lt
  | Top_idx

type kind =
    Tkind_type
  | Tkind_sing of con
  | Tkind_pi of kind * kind     (* binds *)
  (* | Ksigma of kind * kind  (\* binds *\) *)
  | Tkind_unit

and con =
    Tcon_int
  | Tcon_string
  | Tcon_bool
  | Tcon_var of int
  | Tcon_prod of con list * string list option
  | Tcon_arrow of con list * con
  | Tcon_lam of kind * con     (* binds *)
  | Tcon_app of con * con
  | Tcon_forall of kind * con  (* binds *)
  | Tcon_array of con
  (* | Tcon_array of con * expr option *)
  (* | Cexists of kind * con  (\* binds **\) *)
  | Tcon_ref of con
  | Tcon_named of Var.id
  | Tcon_unit

and iface =
    Tiface_plam of kind * iface * iface (* binds *)
  | Tiface_mthds of string * con list * con
  | Tiface_void

and expr =
    Texpr_var of Var.id
  | Texpr_int of int
  | Texpr_string of string
  | Texpr_bool of bool
  | Texpr_op of op * expr list
  | Texpr_func of (Var.id * mut * con) list * con * stmt
  | Texpr_app of expr * expr list
  | Texpr_tuple of expr list
  | Texpr_ctor of con * (string * expr) list
  | Texpr_con of con (* for decls only *)
  | Texpr_plam of kind * iface * expr
  | Texpr_array of expr list
  | Texpr_field of expr * Var.id
  (* | Eproj of expr * int *)
  (* | Epapp of expr * con *)
  (* | Epack of con * expr * con *)
  (* | Eunpack of variable * expr * expr   (\* binds *\) *)

and stmt =
    Tstmt_expr of expr
  | Tstmt_blk of stmt list
  | Tstmt_ret of expr
  | Tstmt_if of expr * stmt * stmt
  | Tstmt_while of expr * stmt
  | Tstmt_decl of Var.id * mut * con option * expr
  | Tstmt_asgn of expr * expr
