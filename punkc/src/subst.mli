open Ast

val subst_kind: con -> kind -> kind
val subst_con: con -> con -> con
val subst_expr: con -> expr -> expr

val lift_kind: int -> kind -> kind
val lift_con: int -> con -> con
val lift_expr: int -> expr -> expr

