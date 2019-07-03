namespace backend

open ir.Ir
open Errors

module Backend =
    type Backend() =
        let mutable env = Env.emptyEnv()

        member this.emit mdl =
            let emitter = Emit.newEmitter()
            emitter.EmitModule env mdl |> ignore
            // printfn "%A" (emitter.get_module())
            emitter.GetModule()

        member this.llvmGen mdl = Llvm_gen.genModule mdl
        member this.compile code =
            code
            |> this.emit
            |> this.llvmGen
