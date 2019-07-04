module Llvm_gen

open System.Collections.Generic
open Bir
open Errors
open Config

let rec genType mdl ctx t =
    match t with
    | Bir_integer_type -> Llvm.llvmIntegerType ctx 64u
    | Bir_boolean_type -> Llvm.llvmIntegerType ctx 1u
    | Bir_byte_type -> Llvm.llvmIntegerType ctx 8u
    | Bir_pointer_type p -> Llvm.llvmPointerType (genType mdl ctx p)
    | Bir_unit_type -> Llvm.llvmVoidType ctx
    | Bir_function_type(r, ts) ->
        Llvm.llvmPointerType (genFuncType mdl ctx (r, ts))
    | Bir_struct_type ts ->
        Llvm.llvmStructType ctx (Array.map (genType mdl ctx) ts)
    | Bir_named_struct_type(n, _) -> Llvm.llvmNamedStructType ctx n
    | Bir_var_arg_function_type(r, ts) ->
        Llvm.llvmPointerType (genVarArgFuncType mdl ctx (r, ts))

and genFuncType mdl ctx (r, ts) =
    Llvm.llvmFunctionType (genType mdl ctx r) (Array.map (genType mdl ctx) ts)

and genVarArgFuncType mdl ctx (r, ts) =
    Llvm.llvmVarArgFunctionType
        (genType mdl ctx r) (Array.map (genType mdl ctx) ts)

let declType mdl ctx (_, t) =
    match t with
    | Bir_named_struct_type(name, _) ->
        Llvm.llvmNamedStructType ctx name |> ignore
    | _ -> raise (BackendException "Only named user struct type can be declared.")

let defType mdl ctx (_, t) =
    match t with
    | Bir_named_struct_type(name, ts) ->
        let s = Llvm.llvmNamedStructType ctx name
        Llvm.llvmStructSetBody
            s (Array.map (genType mdl ctx) !ts) false |> ignore
    | _ -> raise (BackendException "Only named user struct type can be generated.")

let declFunction mdl ctx (env : Dictionary<_, _>) (name, v) =
    let genParam f i (id, _) =
        let p = Llvm.llvmParam f (uint32 i)
        env.Add(string id, p)
    match v with
    | (id, Bir_function(_, vs, t, name, attrs)) ->
        let ft =
            if attrs.is_var_arg then
                genVarArgFuncType mdl ctx t
            else
                genFuncType mdl ctx t
        let f = Llvm.llvmDeclareFunction name ft mdl
        Array.iteri (genParam f) vs
        env.Add(string id, f)
    | _ -> raise (BackendException "Function value expected for func declaration.")

let genOp o =
    match o with
    | Icmp_eq -> Llvm.Icmp.Eq
    | Icmp_slt -> Llvm.Icmp.Slt

let rec genValue mdl ctx
    (env : Dictionary<_, _>) (benv : Dictionary<_, _>) builder (id, v) =
    let sid = string id
    match env.TryGetValue(sid) with
    | false, _ ->
        let gen = genValue mdl ctx env benv builder

        let value =
            match v with
            | Bir_nil -> Llvm.llvmConstNull (Llvm.llvmIntegerType ctx 8u)
            | Bir_gep(b, i, s) ->
                Llvm.llvmBuildGEP (gen b) (Array.map gen i) s builder
            | Bir_const_integer i ->
                Llvm.llvmConstInt (Llvm.llvmIntegerType ctx 64u) (uint64 i)
            | Bir_const_boolean b ->
                Llvm.llvmConstInt (Llvm.llvmIntegerType ctx 1u)
                    (System.Convert.ToUInt64(b))
            | Bir_const_struct vs -> Llvm.llvmConstStruct ctx (Array.map gen vs)
            | Bir_load(v, s) -> Llvm.llvmBuildLoad (gen v) s builder
            | Bir_add(v0, v1) -> Llvm.llvmBuildAdd (gen v0) (gen v1) "add" builder
            | Bir_mul(v0, v1) -> Llvm.llvmBuildMul (gen v0) (gen v1) "mul" builder
            | Bir_sub(v0, v1) -> Llvm.llvmBuildSub (gen v0) (gen v1) "sub" builder
            | Bir_icmp(o, v0, v1) ->
                Llvm.llvmBuildIcmp (genOp o) (gen v0) (gen v1) "icmp" builder
            | Bir_call(v0, vs) ->
                Llvm.llvmBuildCall (gen v0) (Array.map gen vs) "call" builder
            | Bir_extractvalue(v, i, s) ->
                Llvm.llvmBuildExtractvalue (gen v) (uint32 i) s builder
            | Bir_insertvalue(b, v, i, s) ->
                Llvm.llvmBuildInsertvalue (gen b) (gen v) (uint32 i) s builder
            | Bir_array_alloca(t, v, s) ->
                Llvm.llvmBuildArrayAlloca (genType mdl ctx t) (gen v) s builder
            | Bir_store(v0, v1) -> Llvm.llvmBuildStore (gen v0) (gen v1) builder
            | Bir_ret v -> Llvm.llvmBuildRet (gen v) builder
            | Bir_undef t -> Llvm.llvmUndef (genType mdl ctx t)
            | Bir_var(_, name) ->
                raise (BackendException "Variables should be already generated.")
            | Bir_global_stringptr(s, n) ->
                Llvm.llvmBuildGlobalStringptr s n builder
            | Bir_cond_br(p, (b0, _, _), (b1, _, _)) ->
                Llvm.llvmBuildCondBr (gen p) (benv.Item(b0))
                    (benv.Item(b1)) builder
            | Bir_br(b, _, _) -> Llvm.llvmBuildBr (benv.Item(b)) builder
            | Bir_alloca(t, s) ->
                Llvm.llvmBuildAlloca (genType mdl ctx t) s builder
            | Bir_function _ ->
                raise (BackendFatalException "Function is not supported in codegen.")
            | Bir_global_ref _ -> env.Item(sid)

        env.Add(sid, value)
        value
    | true, v -> v

let genGlobal mdl ctx (env : Dictionary<_, _>) (name, (gid, v)) =
    let builder = Llvm.llvmBuilder ctx
    match v with
    | Bir_global_ref t ->
        let g = Llvm.llvmDefineGlobal name (Llvm.llvmUndef (genType mdl ctx t)) mdl
        env.Add(string gid, g)
    | _ ->
        raise (BackendFatalException "global reference")

let declBlock mdl ctx (benv : Dictionary<_, _>) func (name, v, ts) =
    let b = Llvm.llvmAppendBlock ctx name func
    benv.Add(name, b)

let genBlock mdl ctx
    (env : Dictionary<_, _>) (benv : Dictionary<_, _>) (name, v, vs) =
    let b = benv.Item(name)
    let builder = Llvm.llvmBuilder ctx
    Llvm.llvmPositionAtEnd b builder
    ignore (Array.map (genValue mdl ctx env benv builder) !vs)

let genFunction mdl ctx (env : Dictionary<_, _>) (_, f) =
    match f with
    | (id, Bir_function(bs, _, _, _, _)) ->
        let func = env.Item(string id)
        let benv = new Dictionary<string, LLVMSharp.LLVMBasicBlockRef>()
        Array.iter (declBlock mdl ctx benv func) !bs
        Array.iter (genBlock mdl ctx env benv) !bs
    | _ -> raise (BackendException "Code generation on non-function values.")

let genModule mdl =
    let ctx = Llvm.llvmCreateContext()
    let llvm_mdl = Llvm.llvmCreateModule ctx mdl.bir_module_name
    let env = new Dictionary<string, Llvm.llvalue>()
    Array.iter (declType llvm_mdl ctx) !mdl.bir_type_decls
    Array.iter (defType llvm_mdl ctx) !mdl.bir_type_decls
    Array.iter (declFunction llvm_mdl ctx env) !mdl.bir_function_decls
    Array.iter (genGlobal llvm_mdl ctx env) !mdl.bir_global_decls
    Array.iter (genFunction llvm_mdl ctx env) !mdl.bir_function_decls
    llvm_mdl
