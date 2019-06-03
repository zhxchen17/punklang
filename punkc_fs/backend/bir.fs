module Bir

exception BirError of string

type bir_context =
    { bir_context_global : bool }

type bir_type =
    | Bir_integer_type
    | Bir_boolean_type
    | Bir_byte_type
    | Bir_pointer_type of bir_type
    | Bir_unit_type
    | Bir_function_type of bir_type * bir_type array
    | Bir_struct_type of bir_type array
    | Bir_named_struct_type of string * bir_type array ref
    | Bir_var_arg_function_type of bir_type * bir_type array

type bir_op =
    | Icmp_eq
    | Icmp_slt

type bir_func_attrs =
    { is_var_arg : bool }

type bir_block = string * bir_value * bir_value array ref

// FIXME reduce tuple elements
and bir_inst =
    | Bir_function of bir_block array ref * bir_value array * (bir_type * bir_type []) * string * bir_func_attrs
    | Bir_nil
    | Bir_gep of bir_value * bir_value array * string
    | Bir_const_integer of int
    | Bir_const_boolean of bool
    | Bir_const_struct of bir_value array
    | Bir_load of bir_value * string
    | Bir_add of bir_value * bir_value
    | Bir_mul of bir_value * bir_value
    | Bir_sub of bir_value * bir_value
    | Bir_icmp of bir_op * bir_value * bir_value
    | Bir_call of bir_value * bir_value array
    | Bir_extractvalue of bir_value * int * string
    | Bir_insertvalue of bir_value * bir_value * int * string
    | Bir_array_alloca of bir_type * bir_value * string
    | Bir_store of bir_value * bir_value
    | Bir_ret of bir_value
    | Bir_undef of bir_type
    | Bir_var of bir_type * string ref
    | Bir_global_stringptr of string * string
    | Bir_cond_br of bir_value * bir_block * bir_block
    | Bir_br of bir_block
    | Bir_alloca of bir_type * string
    | Bir_global_ref of bir_type

and bir_value = int * bir_inst

type bir_module =
    { bir_module_name : string
      bir_function_decls : (string * bir_value) array ref
      bir_type_decls : (string * bir_type) array ref
      bir_global_decls : (string * bir_value) array ref }

type bir_builder =
    { bir_current_block : bir_block ref }

let counter = ref 0

let next_id() =
    let ret = !counter
    counter := !counter + 1
    ret

let create_context() = { bir_context_global = true }
let integer_type ctx = Bir_integer_type
let byte_type ctx = Bir_byte_type
let boolean_type ctx = Bir_boolean_type
let pointer_type t = Bir_pointer_type t
let void_type ctx = Bir_unit_type
let function_type tout tin = Bir_function_type(tout, Array.ofList tin)
let var_arg_function_type tout tin =
    Bir_var_arg_function_type(tout, Array.ofList tin)
let struct_type ctx ts = Bir_struct_type(Array.ofList ts)

let undef t = (next_id(), Bir_undef t)
let const_int i = (next_id(), Bir_const_integer i)
let const_bool b = (next_id(), Bir_const_boolean b)
let const_nil() = (next_id(), Bir_nil)
let const_struct ctx ts = (next_id(), Bir_const_struct ts)

let find (a : ('a * 'b) []) f =
    let rec find (a : ('a * 'b) []) f n =
        if f a.[n] then
            match a.[n] with
            | (_, x) -> Some x
        else find a f (n + 1)
    try
        find a f 0
    with _ -> None

let type_by_name name mdl = find !mdl.bir_type_decls (fun (s, _) -> s = name)

let named_struct_type ctx name mdl =
    match type_by_name name mdl with
    | None ->
        let ty = Bir_named_struct_type(name, ref [||])
        mdl.bir_type_decls := Array.append !mdl.bir_type_decls [| (name, ty) |]
        ty
    | Some ty -> ty

let struct_set_body t ts packed =
    match t with
    | Bir_named_struct_type(_, fields) -> fields := Array.ofList ts
    | _ -> raise (BirError "named_struct_type expected in struct_set_body()")

let struct_element_types ty =
    match ty with
    | Bir_named_struct_type(_, fields) -> !fields
    | _ -> raise (BirError "named struct type expected in struct_elem_types()")

let create_module ctx name =
    { bir_module_name = name
      bir_function_decls = ref [||]
      bir_type_decls = ref [||]
      bir_global_decls = ref [||] }

let lookup_function name mdl =
    find !mdl.bir_function_decls (fun (fname, _) -> fname = name)

let lookup_global name mdl =
    find !mdl.bir_global_decls (fun (gname, _) -> gname = name)

let define_global name t mdl =
    let nid = next_id()
    let gbl = (nid, Bir_global_ref t)
    mdl.bir_global_decls
    := Array.append !mdl.bir_global_decls [| (name, gbl) |]
    gbl

let declare_global name t mdl =
    let opt = lookup_global name mdl
    match opt with
    | Some x -> x
    | None -> define_global name t mdl

let make_param t = (next_id(), Bir_var(t, ref "p"))

let set_param_name s v =
    match v with
    | (_, Bir_var(_, name)) -> name := s
    | _ -> raise (BirError "the given bir value doesn't represents a parameter")

let get_params f =
    match f with
    | (_, Bir_function(_, p, _, _, _)) -> p
    | _ -> raise (BirError "the given bir value is not a function")

let declare_function name ftype mdl =
    match lookup_function name mdl with
    | None ->
        (match ftype with
         | Bir_function_type(tr, tin) ->
             let func =
                 (next_id(),
                  Bir_function (ref [||], Array.map make_param tin, (tr, tin), name, { is_var_arg = false }))
             mdl.bir_function_decls
             := Array.append !mdl.bir_function_decls [| (name, func) |]
             func
         | Bir_var_arg_function_type(tr, tin) ->
             let func =
                 (next_id(),
                  Bir_function (ref [||], Array.map make_param tin, (tr, tin), name, { is_var_arg = true }))
             mdl.bir_function_decls
             := Array.append !mdl.bir_function_decls [| (name, func) |]
             func
         | _ -> raise (BirError "function type mismatch for declaration"))
    | Some func -> func

let append_block ctx name func =
    match func with
    | (_, Bir_function(blks, _, _, _, _)) ->
        let tail = (name + (string (next_id())), func, ref [||])
        blks := Array.append !blks [| tail |]
        tail
    | _ -> raise (BirError "function expected in append_block")

let block_parent (_, f, _) = f
let insertion_block mdl = !mdl.bir_current_block
let make_builder ctx =
    { bir_current_block = ref ("global", (next_id(), Bir_nil), ref [||]) }

let append_inst v (_, _, blk) =
    blk := Array.append !blk [| v |]
    v

let position_at_end blk mdl = mdl.bir_current_block := blk

let build_struct_gep b i f mdl =
    let inst =
        Bir_gep(b,
                [| (next_id(), Bir_const_integer 0)
                   (next_id(), Bir_const_integer i) |], f)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_gep b indices name mdl =
    let inst = Bir_gep(b, Array.ofList indices, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_load v name mdl =
    let inst = Bir_load(v, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_store v p mdl =
    let inst = Bir_store(v, p)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_add lhs rhs mdl =
    let inst = Bir_add(lhs, rhs)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_mul lhs rhs mdl =
    let inst = Bir_mul(lhs, rhs)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_sub lhs rhs mdl =
    let inst = Bir_sub(lhs, rhs)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_icmp op lhs rhs mdl =
    let inst = Bir_icmp(op, lhs, rhs)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_call f args name mdl =
    let inst = Bir_call(f, args)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_extractvalue b i name mdl =
    let inst = Bir_extractvalue(b, i, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_insertvalue b v i name mdl =
    let inst = Bir_insertvalue(b, v, i, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_array_alloca t n name mdl =
    let inst = Bir_array_alloca(t, n, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_alloca t name mdl =
    let inst = Bir_alloca(t, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_ret v mdl =
    let inst = Bir_ret v
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_global_stringptr s name mdl =
    let inst = Bir_global_stringptr(s, name)
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_br b mdl =
    let inst = Bir_br b
    append_inst (next_id(), inst) !mdl.bir_current_block

let build_cond_br p then_bb else_bb mdl =
    let inst = Bir_cond_br(p, then_bb, else_bb)
    append_inst (next_id(), inst) !mdl.bir_current_block
