open Bir
open Utils

let rec gen_type mdl ctx t =
  match t with
  | Bir_integer_type -> Llvm.integer_type ctx 64
  | Bir_boolean_type -> Llvm.integer_type ctx 1
  | Bir_byte_type -> Llvm.integer_type ctx 8
  | Bir_pointer_type p -> Llvm.pointer_type (gen_type mdl ctx p)
  | Bir_unit_type -> Llvm.void_type ctx
  | Bir_function_type (r, ts) ->
    Llvm.function_type (gen_type mdl ctx r)
      (Array.map (gen_type mdl ctx) ts)
  | Bir_struct_type ts ->
    Llvm.struct_type ctx (Array.map (gen_type mdl ctx) ts)
  | Bir_named_struct_type (n, _) ->
    Llvm.named_struct_type ctx n
  | Bir_var_arg_function_type (r, ts) ->
    Llvm.var_arg_function_type (gen_type mdl ctx r)
      (Array.map (gen_type mdl ctx) ts)

let decl_type mdl ctx (_, t) =
  match t with
  | Bir_named_struct_type (name, _) ->
    ignore (Llvm.named_struct_type ctx name)
  | _ -> raise (Error "Only named user struct type can be declared.")

let def_type mdl ctx (_, t) =
  match t with
  | Bir_named_struct_type (name, ts) ->
    let s = Llvm.named_struct_type ctx name in
    ignore (Llvm.struct_set_body s (Array.map (gen_type mdl ctx) !ts) false)
  | _ -> raise (Error "Only named user struct type can be generated.")

let decl_function mdl ctx env (name, v) =
  let gen_param (id, _) p =
    Hashtbl.add env (string_of_int id) p in
  match v with
  | (id, Bir_function (_, vs, t, name)) ->
    let f = Llvm.declare_function name (gen_type mdl ctx t) mdl in
    Array.iter2 gen_param vs (Llvm.params f);
    Hashtbl.add env (string_of_int id) f
  | _ -> raise (Error "Function value expected for func declaration.")

let gen_op o =
  match o with
  | Icmp_eq -> Llvm.Icmp.Eq
  | Icmp_slt -> Llvm.Icmp.Slt

let rec gen_value mdl ctx env benv builder (id, v) =
  let sid = string_of_int id in
  match Hashtbl.find_opt env sid with
  | None ->
    let gen = gen_value mdl ctx env benv builder in
    let value =
      match v with
      | Bir_nil -> Llvm.const_null (Llvm.integer_type ctx 8)
      | Bir_gep (b, i, s) ->
        Llvm.build_gep (gen b) (Array.map gen i) s builder
      | Bir_const_integer i -> Llvm.const_int (Llvm.integer_type ctx 64) i
      | Bir_const_boolean b ->
        Llvm.const_int (Llvm.integer_type ctx 1) (int_of_bool b)
      | Bir_const_struct vs ->
        Llvm.const_struct ctx (Array.map gen vs)
      | Bir_load (v, s) ->
        Llvm.build_load (gen v) s builder
      | Bir_add (v0, v1) ->
        Llvm.build_add (gen v0) (gen v1) "add" builder
      | Bir_mul (v0, v1) ->
        Llvm.build_mul (gen v0) (gen v1) "mul" builder
      | Bir_sub (v0, v1) ->
        Llvm.build_sub (gen v0) (gen v1) "sub" builder
      | Bir_icmp (o, v0, v1) ->
        Llvm.build_icmp (gen_op o) (gen v0) (gen v1) "icmp" builder
      | Bir_call (v0, vs) ->
        Llvm.build_call (gen v0) (Array.map gen vs) "call" builder
      | Bir_extractvalue (v, i, s) ->
        Llvm.build_extractvalue (gen v) i s builder
      | Bir_insertvalue (b, v, i, s) ->
        Llvm.build_insertvalue (gen b) (gen v) i s builder
      | Bir_array_alloca (t, v, s) ->
        Llvm.build_array_alloca (gen_type mdl ctx t) (gen v) s builder
      | Bir_store (v0, v1) ->
        Llvm.build_store (gen v0) (gen v1) builder
      | Bir_ret v ->
        Llvm.build_ret (gen v) builder
      | Bir_undef t ->
        Llvm.undef (gen_type mdl ctx t)
      | Bir_var (_, name) ->
        raise (Error "Variables should be already generated.")
      | Bir_global_stringptr (s, n) ->
        Llvm.build_global_stringptr s n builder
      | Bir_cond_br (p, (b0, _, _), (b1, _, _)) ->
        Llvm.build_cond_br (gen p) (Hashtbl.find benv b0) (Hashtbl.find benv b1)
          builder
      | Bir_br (b, _, _) ->
        Llvm.build_br (Hashtbl.find benv b) builder
      | Bir_alloca (t, s) ->
        Llvm.build_alloca (gen_type mdl ctx t) s builder
      | Bir_function _ ->
        raise (Fatal "Function is not supported in codegen.")
    in
    Hashtbl.add env sid value;
    value
  | Some v -> v

let gen_global mdl ctx env (name, gid, v) =
  let empty = Hashtbl.create 0 in
  let builder = Llvm.builder ctx in
  let g = Llvm.define_global name (gen_value mdl ctx env empty builder v) mdl in
  Hashtbl.add env (string_of_int gid) g

let decl_block mdl ctx benv func (name, v, ts) =
  let b = Llvm.append_block ctx name func in
  Hashtbl.add benv name b

let gen_block mdl ctx env benv (name, v, vs) =
  let b = Hashtbl.find benv name in
  let builder = Llvm.builder ctx in
  Llvm.position_at_end b builder;
  ignore (Array.map (gen_value mdl ctx env benv builder) !vs)

let gen_function mdl ctx env (name, f) =
  match f with
  | (id, Bir_function (bs, _, _, _)) ->
    let func = Hashtbl.find env (string_of_int id) in
    let benv = Hashtbl.create table_size in
    Array.iter (decl_block mdl ctx benv func) !bs;
    Array.iter (gen_block mdl ctx env benv) !bs
  | _ -> raise (Error "Code generation on non-function values.")

let gen_module { bir_module_name;
                 bir_global_decls;
                 bir_type_decls;
                 bir_function_decls } =
  let ctx = Llvm.create_context () in
  let mdl = Llvm.create_module ctx bir_module_name in
  let env : (string, Llvm.llvalue) Hashtbl.t =
    Hashtbl.create Utils.table_size in
  Array.iter (decl_type mdl ctx) !bir_type_decls;
  Array.iter (def_type mdl ctx) !bir_type_decls;
  Array.iter (decl_function mdl ctx env) !bir_function_decls;
  Array.iter (gen_global mdl ctx env) !bir_global_decls;
  Array.iter (gen_function mdl ctx env) !bir_function_decls;
  mdl
