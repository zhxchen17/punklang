namespace frontend

module Frontend =
    open FSharp.Text.Lexing
    open Errors
    open Tir

    (* Parse a string into an ast *)
    let parse s =
        let lexbuf = LexBuffer<char>.FromString s
        let ast = Parser.prog Lexer.read lexbuf
        ast

    let parse_expr s =
        let lexbuf = LexBuffer<char>.FromString s
        let ast = Parser.term Lexer.read lexbuf
        ast

    type Frontend() =
        let mutable env = Env.emptyEnv()

        // member private this.extractId stmt =
        //     match stmt with
        //     | Tstmt_decl((id, Some name), _, _, _) when id >= 0 ->
        //         env <- Env.addId env id name
        //     | Tstmt_struct((id, Some name), _) when id >= 0 ->
        //         env <- Env.addId env id name
        //     | Tstmt_decl((id, _), _, _, _) when id < 0 ->
        //         raise (Fatal "TODO Frontend.extractId")
        //     | Tstmt_struct((id, _), _) when id < 0 ->
        //         raise (Fatal "TODO Frontend.extractId")
        //     | _ -> ()

        member this.parse s =
            let stmt_list = parse s
            // List.iter this.extractId stmt_list
            stmt_list

        member this.resolve prog =
            Resolve.resolveModule env prog

        member this.elaborate prog =
            Elaborate.elabModule env prog

        member this.typeCheck prog =
            Check.checkModule env prog

        member this.compile code =
            code
            |> this.parse
            |> this.resolve
            |> this.elaborate
            |> this.typeCheck
