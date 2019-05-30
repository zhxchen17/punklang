module Attrs

open Tir
open ir.Ast

let translate_attrs x =
    match x with
    | Tmut -> Mutable
    | Timm -> Immutable
