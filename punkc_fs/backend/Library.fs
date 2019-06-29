namespace backend

open ir.Ast
open Errors

module Backend =
    type Backend() =
        let mutable env = Env.empty_env()

        member this.emit mdl =
            let emitter = Emit.new_emitter()
            emitter.emit_module env mdl |> ignore
            // printfn "%A" (emitter.get_module())
            emitter.get_module()

        member this.llvm_gen mdl = Llvm_gen.gen_module mdl
        member this.compile code =
            code
            |> this.emit
            |> this.llvm_gen
