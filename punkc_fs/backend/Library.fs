namespace backend

open ir.Ast
open Errors

module Backend =
    type Backend() =
        let mutable env = Env.empty_env()

        member this.analyze prog =
            match Analysis.check_mut_stmt env (Sblk prog) with
            | Sblk sl -> sl
            | _ -> raise (BackendFatal "failed to unpack analyzed program")

        member this.emit prog =
            let emitter = Emit.new_emitter()
            emitter.emit_module env (List.toArray prog) |> ignore
            // printfn "%A" (emitter.get_module())
            emitter.get_module()

        member this.llvm_gen mdl = Llvm_gen.gen_module mdl
        member this.compile code =
            code
            |> this.analyze
            |> this.emit
            |> this.llvm_gen
