module Llvm

open System.Runtime.InteropServices
open LLVMSharp

type llvalue = LLVMValueRef

let llvmTrue = new LLVMBool(1)
let llvmFalse = new LLVMBool(0)
let llvmCreateContext() = LLVM.ContextCreate()
let llvmCreateModule ctx name = LLVM.ModuleCreateWithNameInContext(name, ctx)
let llvmIntegerType ctx b = LLVM.IntTypeInContext(ctx, b)
let llvmPointerType t = LLVM.PointerType(t, 0u)
let llvmVoidType ctx = LLVM.VoidTypeInContext(ctx)
let llvmFunctionType tr tp = LLVM.FunctionType(tr, tp, false)
let llvmStructType ctx ts = LLVM.StructTypeInContext(ctx, ts, false)
let llvmNamedStructType ctx name = LLVM.StructCreateNamed(ctx, name)
let llvmVarArgFunctionType tr tp = LLVM.FunctionType(tr, tp, true)
let llvmStructSetBody t b packed = LLVM.StructSetBody(t, b, packed)

let llvmDeclareFunction name t mdl =
    let f = LLVM.GetNamedFunction(mdl, name)
    if f.Pointer.Equals(0n) then LLVM.AddFunction(mdl, name, t)
    else f

let llvmParam f i = LLVM.GetParam(f, i)

let llvmDefineGlobal name g mdl =
    let gv = LLVM.AddGlobal(mdl, LLVM.TypeOf(g), name)
    LLVM.SetInitializer(gv, g)
    gv

let llvmAppendBlock ctx name func = LLVM.AppendBasicBlockInContext(ctx, func, name)
let llvmPositionAtEnd b builder = LLVM.PositionBuilderAtEnd(builder, b)
let llvmConstNull t = LLVM.ConstNull(t)
let llvmConstInt t w = LLVM.ConstInt(t, w, llvmTrue)
let llvmConstStruct ctx vs = LLVM.ConstStructInContext(ctx, vs, false)
let llvmBuilder ctx = LLVM.CreateBuilderInContext(ctx)
let llvmBuildGEP b i s builder = LLVM.BuildGEP(builder, b, i, s)
let llvmBuildLoad v s builder = LLVM.BuildLoad(builder, v, s)
let llvmBuildAdd v0 v1 n builder = LLVM.BuildAdd(builder, v0, v1, n)
let llvmBuildMul v0 v1 n builder = LLVM.BuildMul(builder, v0, v1, n)
let llvmBuildSub v0 v1 n builder = LLVM.BuildSub(builder, v0, v1, n)
let llvmBuildIcmp o v0 v1 n builder = LLVM.BuildICmp(builder, o, v0, v1, n)
let llvmBuildCall f vs n builder = LLVM.BuildCall(builder, f, vs, n)
let llvmBuildExtractvalue v i s builder = LLVM.BuildExtractValue(builder, v, i, s)
let llvmBuildInsertvalue b v i s builder =
    LLVM.BuildInsertValue(builder, b, v, i, s)
let llvmBuildArrayAlloca t v s builder = LLVM.BuildArrayAlloca(builder, t, v, s)
let llvmBuildStore v0 v1 builder = LLVM.BuildStore(builder, v0, v1)
let llvmBuildRet v builder = LLVM.BuildRet(builder, v)
let llvmUndef t = LLVM.GetUndef(t)
let llvmBuildGlobalStringptr s n builder =
    LLVM.BuildGlobalStringPtr(builder, s, n)
let llvmBuildCondBr p b0 b1 builder = LLVM.BuildCondBr(builder, p, b0, b1)
let llvmBuildBr b builder = LLVM.BuildBr(builder, b)
let llvmBuildAlloca t s builder = LLVM.BuildAlloca(builder, t, s)

module Icmp =
    let Eq = LLVMIntPredicate.LLVMIntEQ
    let Slt = LLVMIntPredicate.LLVMIntSLT
