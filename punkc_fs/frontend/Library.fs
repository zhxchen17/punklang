namespace frontend

module Frontend =
    open FSharp.Text.Lexing
    open Errors
    open Tir
    open ir.Ast

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
        let mutable env = Env.empty_env()

        member private this.extract_id stmt =
            match stmt with
            | Tstmt_decl((id, Some name), _, _, _) when id >= 0 ->
                env <- Env.add_id env id name
            | Tstmt_decl((id, _), _, _, _) when id < 0 ->
                raise (Fatal "id is negative")
            | _ -> ()

        member this.parse s =
            let stmt_list = parse s
            List.iter this.extract_id stmt_list
            stmt_list

        member this.resolve prog =
            match Resolve.resolve_stmt env (Tstmt_blk prog) with
            | Tstmt_blk sl -> sl
            | _ -> raise (Fatal "failed to unpack resolved program")

        member this.elaborate prog =
            match Elaborate.elab_stmt env (Tstmt_blk prog) with
            | Tstmt_blk sl -> sl
            | _ -> raise (Fatal "failed to unpack elaborated program")

        member this.type_check prog =
            match Check.check_stmt env (Tstmt_blk prog) with
            | Sblk sl -> sl
            | _ -> raise (Fatal "failed to unpack type checked program")

        member this.compile code =
            code
            |> this.parse
            |> this.resolve
            |> this.elaborate
            |> this.type_check
