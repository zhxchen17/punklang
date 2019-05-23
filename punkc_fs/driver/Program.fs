open System
open System.IO
open frontend.Frontend
open backend.Backend
open LLVMSharp

[<EntryPoint>]
let main argv =
    let frontend = new Frontend()
    let str = File.ReadAllText argv.[0]
    let stmts = frontend.compile str
    let backend = new Backend()
    let llvm_mdl = backend.compile stmts
    LLVM.DumpModule(llvm_mdl);
    0
