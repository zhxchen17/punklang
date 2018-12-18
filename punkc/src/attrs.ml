open Tir
open Ast

let translate_attrs x =
  match x with
    Tmut -> Mutable
  | Timm -> Immutable
