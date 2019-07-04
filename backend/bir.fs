module Bir

open Errors

type BirContext =
    { bir_context_global : bool }

type BirType =
    | Bir_integer_type
    | Bir_boolean_type
    | Bir_byte_type
    | Bir_pointer_type of BirType
    | Bir_unit_type
    | Bir_function_type of BirType * BirType array
    | Bir_struct_type of BirType array
    | Bir_named_struct_type of string * BirType array ref
    | Bir_var_arg_function_type of BirType * BirType array

type BirOp =
    | Icmp_eq
    | Icmp_slt

type BirFuncAttrs =
    { is_var_arg : bool }

type BirBlock = string * BirValue * BirValue array ref

// FIXME reduce tuple elements
and BirInst =
    | Bir_function of BirBlock array ref * BirValue array * (BirType * BirType []) * string * BirFuncAttrs
    | Bir_nil
    | Bir_gep of BirValue * BirValue array * string
    | Bir_const_integer of int
    | Bir_const_boolean of bool
    | Bir_const_struct of BirValue array
    | Bir_load of BirValue * string
    | Bir_add of BirValue * BirValue
    | Bir_mul of BirValue * BirValue
    | Bir_sub of BirValue * BirValue
    | Bir_icmp of BirOp * BirValue * BirValue
    | Bir_call of BirValue * BirValue array
    | Bir_extractvalue of BirValue * int * string
    | Bir_insertvalue of BirValue * BirValue * int * string
    | Bir_array_alloca of BirType * BirValue * string
    | Bir_store of BirValue * BirValue
    | Bir_ret of BirValue
    | Bir_undef of BirType
    | Bir_var of BirType * string ref
    | Bir_global_stringptr of string * string
    | Bir_cond_br of BirValue * BirBlock * BirBlock
    | Bir_br of BirBlock
    | Bir_alloca of BirType * string
    | Bir_global_ref of BirType

and BirValue = int * BirInst

type BirModule =
    { bir_module_name : string
      bir_function_decls : (string * BirValue) array ref
      bir_type_decls : (string * BirType) array ref
      bir_global_decls : (string * BirValue) array ref }

type BirBuilder =
    { bir_current_block : BirBlock ref }

let counter = ref 0

let nextId() =
    let ret = !counter
    counter := !counter + 1
    ret

let createContext() = { bir_context_global = true }
let integerType ctx = Bir_integer_type
let byteType ctx = Bir_byte_type
let booleanType ctx = Bir_boolean_type
let pointerType t = Bir_pointer_type t
let voidType ctx = Bir_unit_type
let functionType tout tin = Bir_function_type(tout, Array.ofList tin)
let varArgFunctionType tout tin =
    Bir_var_arg_function_type(tout, Array.ofList tin)
let structType ctx ts = Bir_struct_type(Array.ofList ts)

let undef t = (nextId(), Bir_undef t)
let constInt i = (nextId(), Bir_const_integer i)
let constBool b = (nextId(), Bir_const_boolean b)
let constNil() = (nextId(), Bir_nil)
let constStruct ctx ts = (nextId(), Bir_const_struct ts)

let find (a : ('a * 'b) []) f =
    let rec find (a : ('a * 'b) []) f n =
        if f a.[n] then
            match a.[n] with
            | (_, x) -> Some x
        else find a f (n + 1)
    try
        find a f 0
    with _ -> None

let typeByName name mdl = find !mdl.bir_type_decls (fun (s, _) -> s = name)

let namedStructType ctx name mdl =
    match typeByName name mdl with
    | None ->
        let ty = Bir_named_struct_type(name, ref [||])
        mdl.bir_type_decls := Array.append !mdl.bir_type_decls [| (name, ty) |]
        ty
    | Some ty -> ty

let structSetBody t ts packed =
    match t with
    | Bir_named_struct_type(_, fields) -> fields := Array.ofList ts
    | _ -> raise (BackendBirException "TODO structSetBody")

let structElementTypes ty =
    match ty with
    | Bir_named_struct_type(_, fields) -> !fields
    | _ -> raise (BackendBirException "TODO structElementTypes")

let createModule ctx name =
    { bir_module_name = name
      bir_function_decls = ref [||]
      bir_type_decls = ref [||]
      bir_global_decls = ref [||] }

let lookupFunction name mdl =
    find !mdl.bir_function_decls (fun (fname, _) -> fname = name)

let lookupGlobal name mdl =
    find !mdl.bir_global_decls (fun (gname, _) -> gname = name)

let defineGlobal name t mdl =
    let nid = nextId()
    let gbl = (nid, Bir_global_ref t)
    mdl.bir_global_decls
    := Array.append !mdl.bir_global_decls [| (name, gbl) |]
    gbl

let declareGlobal name t mdl =
    let opt = lookupGlobal name mdl
    match opt with
    | Some x -> x
    | None -> defineGlobal name t mdl

let makeParam t = (nextId(), Bir_var(t, ref "p"))

let setParamName s v =
    match v with
    | (_, Bir_var(_, name)) -> name := s
    | _ -> raise (BackendBirException "TOOD setParamName")

let getParams f =
    match f with
    | (_, Bir_function(_, p, _, _, _)) -> p
    | _ -> raise (BackendBirException "TODO getParams")

let declareFunction name ftype mdl =
    match lookupFunction name mdl with
    | None ->
        (match ftype with
         | Bir_function_type(tr, tin) ->
             let func =
                 (nextId(),
                  Bir_function (ref [||], Array.map makeParam tin, (tr, tin), name, { is_var_arg = false }))
             mdl.bir_function_decls
             := Array.append !mdl.bir_function_decls [| (name, func) |]
             func
         | Bir_var_arg_function_type(tr, tin) ->
             let func =
                 (nextId(),
                  Bir_function (ref [||], Array.map makeParam tin, (tr, tin), name, { is_var_arg = true }))
             mdl.bir_function_decls
             := Array.append !mdl.bir_function_decls [| (name, func) |]
             func
         | _ -> raise (BackendBirException "TODO declareFunction"))
    | Some func -> func

let appendBlock ctx name func =
    match func with
    | (_, Bir_function(blks, _, _, _, _)) ->
        let tail = (name + (string (nextId())), func, ref [||])
        blks := Array.append !blks [| tail |]
        tail
    | _ -> raise (BackendBirException "TODO appendBlock")

let blockParent (_, f, _) = f
let insertionBlock mdl = !mdl.bir_current_block
let makeBuilder ctx =
    { bir_current_block = ref ("global", (nextId(), Bir_nil), ref [||]) }

let appendInst v (_, _, blk) =
    blk := Array.append !blk [| v |]
    v

let positionAtEnd blk mdl = mdl.bir_current_block := blk

let buildStructGEP b i f mdl =
    let inst =
        Bir_gep(b,
                [| (nextId(), Bir_const_integer 0)
                   (nextId(), Bir_const_integer i) |], f)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildGEP b indices name mdl =
    let inst = Bir_gep(b, Array.ofList indices, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildLoad v name mdl =
    let inst = Bir_load(v, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildStore v p mdl =
    let inst = Bir_store(v, p)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildAdd lhs rhs mdl =
    let inst = Bir_add(lhs, rhs)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildMul lhs rhs mdl =
    let inst = Bir_mul(lhs, rhs)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildSub lhs rhs mdl =
    let inst = Bir_sub(lhs, rhs)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildIcmp op lhs rhs mdl =
    let inst = Bir_icmp(op, lhs, rhs)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildCall f args name mdl =
    let inst = Bir_call(f, args)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildExtractvalue b i name mdl =
    let inst = Bir_extractvalue(b, i, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildInsertvalue b v i name mdl =
    let inst = Bir_insertvalue(b, v, i, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildArrayAlloca t n name mdl =
    let inst = Bir_array_alloca(t, n, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildAlloca t name mdl =
    let inst = Bir_alloca(t, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildRet v mdl =
    let inst = Bir_ret v
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildGlobalStringptr s name mdl =
    let inst = Bir_global_stringptr(s, name)
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildBr b mdl =
    let inst = Bir_br b
    appendInst (nextId(), inst) !mdl.bir_current_block

let buildCondBr p then_bb else_bb mdl =
    let inst = Bir_cond_br(p, then_bb, else_bb)
    appendInst (nextId(), inst) !mdl.bir_current_block
