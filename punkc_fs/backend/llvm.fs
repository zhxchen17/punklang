module Llvm

open System.Runtime.InteropServices
open LLVMSharp

type llvalue = LLVMValueRef

let llvm_true = new LLVMBool(1)
let llvm_false = new LLVMBool(0)
let create_context() = LLVM.ContextCreate()
let create_module ctx name = LLVM.ModuleCreateWithNameInContext(name, ctx)
let integer_type ctx b = LLVM.IntTypeInContext(ctx, b)
let pointer_type t = LLVM.PointerType(t, 0u)
let void_type ctx = LLVM.VoidTypeInContext(ctx)
let function_type tr tp = LLVM.FunctionType(tr, tp, false)
let struct_type ctx ts = LLVM.StructTypeInContext(ctx, ts, false)
let named_struct_type ctx name = LLVM.StructCreateNamed(ctx, name)
let var_arg_function_type tr tp = LLVM.FunctionType(tr, tp, true)
let struct_set_body t b packed = LLVM.StructSetBody(t, b, packed)

let declare_function name t mdl =
    let f = LLVM.GetNamedFunction(mdl, name)
    if f.Pointer.Equals(0n) then LLVM.AddFunction(mdl, name, t)
    else f

let param f i = LLVM.GetParam(f, i)

let define_global name g mdl =
    let gv = LLVM.AddGlobal(mdl, LLVM.TypeOf(g), name)
    LLVM.SetInitializer(gv, g)
    gv

let append_block ctx name func = LLVM.AppendBasicBlockInContext(ctx, func, name)
let position_at_end b builder = LLVM.PositionBuilderAtEnd(builder, b)
let const_null t = LLVM.ConstNull(t)
let const_int t w = LLVM.ConstInt(t, w, llvm_true)
let const_struct ctx vs = LLVM.ConstStructInContext(ctx, vs, false)
let builder ctx = LLVM.CreateBuilderInContext(ctx)
let build_gep b i s builder = LLVM.BuildGEP(builder, b, i, s)
let build_load v s builder = LLVM.BuildLoad(builder, v, s)
let build_add v0 v1 n builder = LLVM.BuildAdd(builder, v0, v1, n)
let build_mul v0 v1 n builder = LLVM.BuildMul(builder, v0, v1, n)
let build_sub v0 v1 n builder = LLVM.BuildSub(builder, v0, v1, n)
let build_icmp o v0 v1 n builder = LLVM.BuildICmp(builder, o, v0, v1, n)
let build_call f vs n builder = LLVM.BuildCall(builder, f, vs, n)
let build_extractvalue v i s builder = LLVM.BuildExtractValue(builder, v, i, s)
let build_insertvalue b v i s builder =
    LLVM.BuildInsertValue(builder, b, v, i, s)
let build_array_alloca t v s builder = LLVM.BuildArrayAlloca(builder, t, v, s)
let build_store v0 v1 builder = LLVM.BuildStore(builder, v0, v1)
let build_ret v builder = LLVM.BuildRet(builder, v)
let undef t = LLVM.GetUndef(t)
let build_global_stringptr s n builder =
    LLVM.BuildGlobalStringPtr(builder, s, n)
let build_cond_br p b0 b1 builder = LLVM.BuildCondBr(builder, p, b0, b1)
let build_br b builder = LLVM.BuildBr(builder, b)
let build_alloca t s builder = LLVM.BuildAlloca(builder, t, s)

module Icmp =
    let Eq = LLVMIntPredicate.LLVMIntEQ
    let Slt = LLVMIntPredicate.LLVMIntSLT
