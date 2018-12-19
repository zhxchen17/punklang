open Ast

val subst_kind: ty -> kind -> kind
val subst_con: ty -> ty -> ty
val subst_expr: ty -> exp -> exp

val lift_kind: int -> kind -> kind
val lift_con: int -> ty -> ty
val lift_expr: int -> exp -> exp

