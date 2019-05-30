module Var

type id = int * string option

let nextvar : int ref = ref 0

let newvar s =
    let res = !nextvar
    nextvar := res + 1
    (res, s)
