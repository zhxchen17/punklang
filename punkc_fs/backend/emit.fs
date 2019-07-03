module Emit

open Bir
open ir.Ir
open Errors

let valueMap x d f =
    match x with
    | Some x' -> f x'
    | None -> d

type Emitter(mdl, context) =
    let intType = integer_type context
    let byteType = byte_type context
    let boolType = boolean_type context
    let strType = pointer_type byteType
    let unitType = void_type context

    let entryBlock =
        let ft = function_type intType [ intType ]
        let theFunction = declare_function "main" ft mdl
        append_block context "entry" theFunction

    let mutable theModule = mdl
    let mutable mainBlock = entryBlock
    let mutable builder = make_builder context
    let mutable currentBlock = entryBlock

    let declarePrintf mdl =
        let ft = var_arg_function_type intType [ pointer_type byteType ]
        declare_function "printf" ft mdl

    let declareExit mdl =
        let ft = function_type unitType [ intType ]
        declare_function "exit" ft mdl

    let getFuncName i = "func_" + (string i)

    let getGlobalName i = "global_" + (string i)

    member private this.EmitRef (env : Env.env) ((_, v) as tv) =
        match v with
        | Evar(id, _) -> env.named_refs.Item(id)
        | Efield(b, (idx, Some f)) ->
            let b = this.EmitRef env b
            assert (idx >= 0)
            build_struct_gep b idx f builder
        | _ -> raise (BackendFatal "rvalue is referenced")

    member private this.SwitchBlock blk =
        let ret = currentBlock
        currentBlock <- blk
        position_at_end blk builder
        ret

    member private this.RestoreBlock blk =
        currentBlock <- blk
        position_at_end blk builder

    member private this.EmitFunc (env : Env.env) (id, vmcl, cr, body) =
        let (i, _) = id
        let fname = getFuncName i
        let ft =
            function_type (this.EmitCon env cr)
                (List.map (fun (_, c) -> this.EmitCon env c) vmcl)
        let theFunction = declare_function fname ft theModule
        let prologue = append_block context "prologue" theFunction
        let parent = this.SwitchBlock prologue
        let setParam i a =
            match (Array.ofList vmcl).[i] with
            | ((id, Some n), c) ->
                set_param_name n a
                let addr = build_alloca (this.EmitCon env c) n builder
                build_store a addr builder |> ignore
                env.named_refs.Add(id, addr)
            | _ -> raise (BackendError "unnamed param")
        Array.iteri setParam (get_params theFunction)
        (* Create a new basic block to start insertion into. *)
        let block = append_block context "entry" theFunction
        build_br block builder |> ignore
        this.SwitchBlock block |> ignore
        this.EmitStmt env body |> ignore
        ignore (build_ret (undef (this.EmitCon env cr)) builder)
        (* Validate the generated code, checking for consistency. *)
        (* Llvm_analysis.assert_valid_function the_function; *)
        this.RestoreBlock parent
        theFunction

    member this.EmitCon env c =
        match c with
        | Cint -> intType
        | Cbool -> boolType
        | Cstring -> strType
        | Cstruct(id, _) ->
            let stl = Env.lookupStruct env id
            let cl = List.map snd stl
            struct_type context (List.map (this.EmitCon env) cl)
        | Carray c -> pointer_type (this.EmitCon env c)
        | Cprod [] -> intType // FIXME
        | Carrow(cl, cr) ->
            function_type (this.EmitCon env cr)
                (List.map (this.EmitCon env) cl)
        | _ -> raise (BackendFatal("unimplemented type emission " + (string c)))

    member this.EmitTexp (env : Env.env) (c, e) =
        match e with
        | Evar(id, n) when id >= 0 ->
            try
                let v = env.named_refs.Item(id)
                build_load v ((Env.mangleName id) + "_ld") builder
            with e ->
                valueMap n () (printf "%s")
                raise e
        | Evar(id, _) when id < 0 ->
            raise (BackendError "unknown variable name")
        | Eint i -> const_int i
        | Estring s -> build_global_stringptr s "string_tmp" builder
        | Ebool b ->
            if b then const_bool true
            else const_bool false
        | Eop(o, el) ->
            (match o with
             | Add ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 build_add lhs rhs builder
             | Multiply ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 build_mul lhs rhs builder
             | Minus ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 build_sub lhs rhs builder
             | Equal ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 build_icmp Icmp_eq lhs rhs builder
             | Cprintf ->
                 let vl = List.map (this.EmitTexp env) el
                 (match lookup_function "printf" theModule with
                  | None -> raise (BackendFatal "printf should be declared")
                  | Some printer ->
                      build_call printer (Array.ofList vl) "unit" builder)
             | Lt ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 build_icmp Icmp_slt lhs rhs builder
             | Idx ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 let p = build_gep lhs [ rhs ] "idx" builder
                 build_load p "ld" builder)
        | Efunc(id, vmcl, cr, body) -> this.EmitFunc env (id, vmcl, cr, body)
        | Efield(b, (i, Some f)) ->
            assert (i >= 0)
            build_extractvalue (this.EmitTexp env b) i f builder
        | Earray(el) ->
            match c with
            | Carray elem_ty ->
                let c' = this.EmitCon env elem_ty
                let l = const_int (List.length el)
                let res = build_array_alloca c' l "array_cns" builder
                let init_elem i e' =
                    let gep = build_gep res [ const_int i ] "gep" builder
                    let _ = build_store (this.EmitTexp env e') gep builder
                    ()
                List.iteri init_elem el
                res
            | _ -> raise (BackendFatal "TODO Emitter.EmitTexp")
        | Ector(Cstruct(_, Some s), sel) ->
            (match type_by_name s theModule with
             | None -> raise (BackendError "TODO Emitter.EmitTexp")
             | Some ty ->
                 let elems = struct_element_types ty
                 let start = const_struct context (Array.map undef elems)
                 let roll =
                     (fun (i, v) e ->
                     (i + 1,
                      build_insertvalue v (this.EmitTexp env e) i "field"
                          builder))
                 let (_, res) = List.fold roll (0, start) (List.map snd sel)
                 res)
        | Eapp(f, args) ->
            build_call (this.EmitTexp env f)
                (Array.ofList (List.map (this.EmitTexp env) args)) "res"
                builder
        | Etuple [] ->
            const_int 0 // FIXME
        | _ ->
            raise (BackendFatal "TODO Emitter.EmitTexp")

    member this.EmitStmt (env : Env.env) s =
        match s with
        | Sret te ->
            let ret = this.EmitTexp env te
            ignore (build_ret ret builder)
        | Sdecl((id, n), ((c, _) as te)) ->
            let c' = this.EmitCon env c
            let value = this.EmitTexp env te
            // FIXME build_alloca -> alloc_box
            let addr =
                build_alloca (this.EmitCon env c) (Env.mangleName id)
                    builder
            ignore (build_store value addr builder)
            env.named_refs.Add(id, addr)
        | Sblk sl ->
            List.iter (this.EmitStmt env) sl
        | Sexpr te ->
            let _ = this.EmitTexp env te in ()
        | Sasgn(lval, te) ->
            ignore
                (build_store (this.EmitTexp env te) (this.EmitRef env lval)
                     builder)
        | Sif(te, s0, s1) ->
            let pred = this.EmitTexp env te
            (* Grab the first block so that we might later add the conditional
         * branch to it at the end of the function. *)
            let startBB = insertion_block builder
            let theFunction = block_parent startBB
            let thenBB = append_block context "then" theFunction
            (* Emit 'then' value. *)
            position_at_end thenBB builder
            this.EmitStmt env s0
            (* Codegen of 'then' can change the current block, update thenBB for
         * the phi. We create a new name because one is used for the phi node,
         * and the other is used for the conditional branch. *)
            let newThenBB = insertion_block builder
            (* Emit 'else' value. *)
            let elseBB = append_block context "else" theFunction
            position_at_end elseBB builder
            this.EmitStmt env s1
            (* Codegen of 'else' can change the current block, update elseBB for
         * the phi. *)
            let newElseBB = insertion_block builder
            (* Emit merge block. *)
            let mergeBB = append_block context "cont" theFunction
            (* Return to the start block to add the conditional branch. *)
            position_at_end startBB builder
            ignore (build_cond_br pred thenBB elseBB builder)
            (* Set a unconditional branch at the end of the 'then' block and the
         * 'else' block to the 'merge' block. *)
            position_at_end newThenBB builder
            ignore (build_br mergeBB builder)
            position_at_end newElseBB builder
            ignore (build_br mergeBB builder)
            (* Finally, set the builder to the end of the merge block. *)
            position_at_end mergeBB builder
        | Swhile(e, s) ->
            let startBB = insertion_block builder
            let theFunction = block_parent startBB
            let condBB = append_block context "cond" theFunction
            position_at_end condBB builder
            let pred = this.EmitTexp env e
            let new_condBB = insertion_block builder
            let loopBB = append_block context "loop" theFunction
            position_at_end loopBB builder
            this.EmitStmt env s
            let new_loopBB = insertion_block builder
            (* Emit merge block. *)
            let mergeBB = append_block context "cont" theFunction
            position_at_end startBB builder
            ignore (build_br condBB builder)
            position_at_end new_condBB builder
            ignore (build_cond_br pred loopBB mergeBB builder)
            position_at_end new_loopBB builder
            ignore (build_br new_condBB builder)
            position_at_end mergeBB builder

    member private this.DeclFunc env s =
        match s with
        | Sdecl((i, n), (c, Efunc _)) ->
            let t = this.EmitCon env c
            let f = declare_global (getGlobalName i) t theModule
            env.named_refs.Add(i, f)
        | _ -> ()

    member this.ScanHeader(env : Env.env) = function
        | ((i, Some s), Dstruct(_, stl)) ->
            named_struct_type context s theModule |> ignore
            env.struct_def.Add(i, stl)
        | (_, Dstruct _) -> raise (BackendFatal "TODO Emitter.ScanHeader")
        | (_, Diface _) -> raise (BackendFatal "TODO Emitter.ScanHeader")
        | (_, Dalias _) -> raise (BackendFatal "TODO Emitter.ScanHeader")

    member this.EmitHeader(env : Env.env) = function
        | ((_, Some s), Dstruct(_, stl)) ->
            let ty = named_struct_type context s theModule
            let tl = List.map snd stl
            struct_set_body ty (List.map (this.EmitCon env) tl) false |> ignore
        | (_, Dstruct _) -> raise (BackendFatal "TODO Emitter.ScanHeader")
        | (_, Diface _) -> raise (BackendFatal "TODO Emitter.ScanHeader")
        | (_, Dalias _) -> raise (BackendFatal "TODO Emitter.ScanHeader")

    member private this.EmitGlobal (env : Env.env) s =
        match s with
        | Sdecl((id, n), ((c, v) as te)) ->
            let parent = this.SwitchBlock mainBlock
            let value = this.EmitTexp env te
            let t = this.EmitCon env c
            let addr = declare_global (getGlobalName id) t theModule
            build_store value addr builder |> ignore
            this.RestoreBlock parent
            // TODO migrate to TryAdd for dotnet core 3.0
            if not (env.named_refs.ContainsKey(id)) then
                env.named_refs.Add(id, addr)
        | _ ->
            this.EmitStmt env s

    member private this.EmitMainPrologue(env : Env.env) =
        let parent = this.SwitchBlock mainBlock
        build_ret (const_int 0) builder |> ignore
        this.RestoreBlock parent

    member this.EmitModule env (tt, prog) =
        declareExit theModule |> ignore
        declarePrintf theModule |> ignore
        List.iter (this.ScanHeader env) tt
        List.iter (this.EmitHeader env) tt
        List.iter (this.DeclFunc env) prog
        List.iter (this.EmitGlobal env) prog
        this.EmitMainPrologue env

    member this.GetModule() = theModule

let newEmitter() =
    let context = create_context()
    let mdl = create_module context "punkage"
    new Emitter(mdl, context)
