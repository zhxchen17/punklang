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

and con =
    | Tcon_int
    | Tcon_string
    | Tcon_bool
    | Tcon_var of int
    | Tcon_prod of con list * string list option
    | Tcon_arrow of con list * con
    (* binds *)
    | Tcon_app of con * con
    (* binds *)
    | Tcon_array of con
    (* | Tcon_array of con * expr option *)
    (* | Cexists of kind * con  (\* binds **\) *)
    | Tcon_ref of con
    | Tcon_named of Var.id
    | Tcon_unit

and expr =
    | Texpr_var of Var.id
    | Texpr_int of int
    | Texpr_string of string
    | Texpr_bool of bool
    | Texpr_op of op * expr list
    | Texpr_func of (Var.id * con) list * con * stmt
    | Texpr_app of expr * expr list
    | Texpr_tuple of expr list
    | Texpr_ctor of con * (string * expr) list
    // | Texpr_plam of kind * iface * expr
    | Texpr_array of expr list
    | Texpr_field of expr * Var.id

(* | Eproj of expr * int *)
(* | Epapp of expr * con *)
(* | Epack of con * expr * con *)
(* | Eunpack of variable * expr * expr   (\* binds *\) *)

and stmt =
    | Tstmt_expr of expr
    | Tstmt_blk of stmt list
    | Tstmt_ret of expr
    | Tstmt_if of expr * stmt * stmt
    | Tstmt_while of expr * stmt
    | Tstmt_decl of Var.id * mut * con option * expr
    | Tstmt_struct of Var.id * (string * con) list
    | Tstmt_asgn of expr * expr
