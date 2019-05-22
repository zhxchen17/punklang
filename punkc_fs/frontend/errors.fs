module Errors

exception Fatal of string
exception Error of string
exception TypeError of string
exception EquivTypeError of string * string * string
exception SyntaxError of string
