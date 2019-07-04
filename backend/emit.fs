module Emit

open Bir
open ir.Ir
open Errors

let valueMap x d f =
    match x with
    | Some x' -> f x'
    | None -> d

type Emitter(mdl, context) =
    let intType = integerType context
    let byteType = byteType context
    let boolType = booleanType context
    let strType = pointerType byteType
    let unitType = voidType context

    let entryBlock =
        let ft = functionType intType [ intType ]
        let theFunction = declareFunction "main" ft mdl
        appendBlock context "entry" theFunction

    let mutable theModule = mdl
    let mutable mainBlock = entryBlock
    let mutable builder = makeBuilder context
    let mutable currentBlock = entryBlock

    let declarePrintf mdl =
        let ft = varArgFunctionType intType [ pointerType byteType ]
        declareFunction "printf" ft mdl

    let declareExit mdl =
        let ft = functionType unitType [ intType ]
        declareFunction "exit" ft mdl

    let getFuncName i = "func_" + (string i)

    let getGlobalName i = "global_" + (string i)

    member private this.EmitRef (env : Env.env) ((_, v) as tv) =
        match v with
        | Evar(id, _) -> env.named_refs.Item(id)
        | Efield(b, (idx, Some f)) ->
            let b = this.EmitRef env b
            assert (idx >= 0)
            buildStructGEP b idx f builder
        | _ -> raise (BackendFatalException "rvalue is referenced")

    member private this.SwitchBlock blk =
        let ret = currentBlock
        currentBlock <- blk
        positionAtEnd blk builder
        ret

    member private this.RestoreBlock blk =
        currentBlock <- blk
        positionAtEnd blk builder

    member private this.EmitFunc (env : Env.env) (id, vmcl, cr, body) =
        let (i, _) = id
        let fname = getFuncName i
        let ft =
            functionType (this.EmitCon env cr)
                (List.map (fun (_, c) -> this.EmitCon env c) vmcl)
        let theFunction = declareFunction fname ft theModule
        let prologue = appendBlock context "prologue" theFunction
        let parent = this.SwitchBlock prologue
        let setParam i a =
            match (Array.ofList vmcl).[i] with
            | ((id, Some n), c) ->
                setParamName n a
                let addr = buildAlloca (this.EmitCon env c) n builder
                buildStore a addr builder |> ignore
                env.named_refs.Add(id, addr)
            | _ -> raise (BackendException "unnamed param")
        Array.iteri setParam (getParams theFunction)
        (* Create a new basic block to start insertion into. *)
        let block = appendBlock context "entry" theFunction
        buildBr block builder |> ignore
        this.SwitchBlock block |> ignore
        this.EmitStmt env body |> ignore
        ignore (buildRet (undef (this.EmitCon env cr)) builder)
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
            structType context (List.map (this.EmitCon env) cl)
        | Carray c -> pointerType (this.EmitCon env c)
        | Cprod [] -> intType // FIXME
        | Carrow(cl, cr) ->
            functionType (this.EmitCon env cr)
                (List.map (this.EmitCon env) cl)
        | _ -> raise (BackendFatalException("unimplemented type emission " + (string c)))

    member this.EmitTexp (env : Env.env) (c, e) =
        match e with
        | Evar(id, n) when id >= 0 ->
            try
                let v = env.named_refs.Item(id)
                buildLoad v ((Env.mangleName id) + "_ld") builder
            with e ->
                valueMap n () (printf "%s")
                raise e
        | Evar(id, _) when id < 0 ->
            raise (BackendException "unknown variable name")
        | Eint i -> constInt i
        | Estring s -> buildGlobalStringptr s "string_tmp" builder
        | Ebool b ->
            if b then constBool true
            else constBool false
        | Eop(o, el) ->
            (match o with
             | Add ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 buildAdd lhs rhs builder
             | Multiply ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 buildMul lhs rhs builder
             | Minus ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 buildSub lhs rhs builder
             | Equal ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 buildIcmp Icmp_eq lhs rhs builder
             | Cprintf ->
                 let vl = List.map (this.EmitTexp env) el
                 (match lookupFunction "printf" theModule with
                  | None -> raise (BackendFatalException "printf should be declared")
                  | Some printer ->
                      buildCall printer (Array.ofList vl) "unit" builder)
             | Lt ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 buildIcmp Icmp_slt lhs rhs builder
             | Idx ->
                 let lhs = this.EmitTexp env (List.item 0 el)
                 let rhs = this.EmitTexp env (List.item 1 el)
                 let p = buildGEP lhs [ rhs ] "idx" builder
                 buildLoad p "ld" builder)
        | Efunc(id, vmcl, cr, body) -> this.EmitFunc env (id, vmcl, cr, body)
        | Efield(b, (i, Some f)) ->
            assert (i >= 0)
            buildExtractvalue (this.EmitTexp env b) i f builder
        | Earray(el) ->
            match c with
            | Carray elem_ty ->
                let c' = this.EmitCon env elem_ty
                let l = constInt (List.length el)
                let res = buildArrayAlloca c' l "array_cns" builder
                let init_elem i e' =
                    let gep = buildGEP res [ constInt i ] "gep" builder
                    let _ = buildStore (this.EmitTexp env e') gep builder
                    ()
                List.iteri init_elem el
                res
            | _ -> raise (BackendFatalException "TODO Emitter.EmitTexp")
        | Ector(Cstruct(_, Some s), sel) ->
            (match typeByName s theModule with
             | None -> raise (BackendException "TODO Emitter.EmitTexp")
             | Some ty ->
                 let elems = structElementTypes ty
                 let start = constStruct context (Array.map undef elems)
                 let roll =
                     (fun (i, v) e ->
                     (i + 1,
                      buildInsertvalue v (this.EmitTexp env e) i "field"
                          builder))
                 let (_, res) = List.fold roll (0, start) (List.map snd sel)
                 res)
        | Eapp(f, args) ->
            buildCall (this.EmitTexp env f)
                (Array.ofList (List.map (this.EmitTexp env) args)) "res"
                builder
        | Etuple [] ->
            constInt 0 // FIXME
        | _ ->
            raise (BackendFatalException "TODO Emitter.EmitTexp")

    member this.EmitStmt (env : Env.env) s =
        match s with
        | Sret te ->
            let ret = this.EmitTexp env te
            ignore (buildRet ret builder)
        | Sdecl((id, n), ((c, _) as te)) ->
            let c' = this.EmitCon env c
            let value = this.EmitTexp env te
            // FIXME build_alloca -> alloc_box
            let addr =
                buildAlloca (this.EmitCon env c) (Env.mangleName id)
                    builder
            ignore (buildStore value addr builder)
            env.named_refs.Add(id, addr)
        | Sblk sl ->
            List.iter (this.EmitStmt env) sl
        | Sexpr te ->
            let _ = this.EmitTexp env te in ()
        | Sasgn(lval, te) ->
            ignore
                (buildStore (this.EmitTexp env te) (this.EmitRef env lval)
                     builder)
        | Sif(te, s0, s1) ->
            let pred = this.EmitTexp env te
            (* Grab the first block so that we might later add the conditional
         * branch to it at the end of the function. *)
            let startBB = insertionBlock builder
            let theFunction = blockParent startBB
            let thenBB = appendBlock context "then" theFunction
            (* Emit 'then' value. *)
            positionAtEnd thenBB builder
            this.EmitStmt env s0
            (* Codegen of 'then' can change the current block, update thenBB for
         * the phi. We create a new name because one is used for the phi node,
         * and the other is used for the conditional branch. *)
            let newThenBB = insertionBlock builder
            (* Emit 'else' value. *)
            let elseBB = appendBlock context "else" theFunction
            positionAtEnd elseBB builder
            this.EmitStmt env s1
            (* Codegen of 'else' can change the current block, update elseBB for
         * the phi. *)
            let newElseBB = insertionBlock builder
            (* Emit merge block. *)
            let mergeBB = appendBlock context "cont" theFunction
            (* Return to the start block to add the conditional branch. *)
            positionAtEnd startBB builder
            ignore (buildCondBr pred thenBB elseBB builder)
            (* Set a unconditional branch at the end of the 'then' block and the
         * 'else' block to the 'merge' block. *)
            positionAtEnd newThenBB builder
            ignore (buildBr mergeBB builder)
            positionAtEnd newElseBB builder
            ignore (buildBr mergeBB builder)
            (* Finally, set the builder to the end of the merge block. *)
            positionAtEnd mergeBB builder
        | Swhile(e, s) ->
            let startBB = insertionBlock builder
            let theFunction = blockParent startBB
            let condBB = appendBlock context "cond" theFunction
            positionAtEnd condBB builder
            let pred = this.EmitTexp env e
            let new_condBB = insertionBlock builder
            let loopBB = appendBlock context "loop" theFunction
            positionAtEnd loopBB builder
            this.EmitStmt env s
            let new_loopBB = insertionBlock builder
            (* Emit merge block. *)
            let mergeBB = appendBlock context "cont" theFunction
            positionAtEnd startBB builder
            ignore (buildBr condBB builder)
            positionAtEnd new_condBB builder
            ignore (buildCondBr pred loopBB mergeBB builder)
            positionAtEnd new_loopBB builder
            ignore (buildBr new_condBB builder)
            positionAtEnd mergeBB builder

    member private this.DeclFunc env s =
        match s with
        | Sdecl((i, n), (c, Efunc _)) ->
            let t = this.EmitCon env c
            let f = declareGlobal (getGlobalName i) t theModule
            env.named_refs.Add(i, f)
        | _ -> ()

    member this.ScanHeader(env : Env.env) = function
        | ((i, Some s), Dstruct(_, stl)) ->
            namedStructType context s theModule |> ignore
            env.struct_def.Add(i, stl)
        | (_, Dstruct _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")
        | (_, Diface _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")
        | (_, Dalias _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")

    member this.EmitHeader(env : Env.env) = function
        | ((_, Some s), Dstruct(_, stl)) ->
            let ty = namedStructType context s theModule
            let tl = List.map snd stl
            structSetBody ty (List.map (this.EmitCon env) tl) false |> ignore
        | (_, Dstruct _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")
        | (_, Diface _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")
        | (_, Dalias _) -> raise (BackendFatalException "TODO Emitter.ScanHeader")

    member private this.EmitGlobal (env : Env.env) s =
        match s with
        | Sdecl((id, n), ((c, v) as te)) ->
            let parent = this.SwitchBlock mainBlock
            let value = this.EmitTexp env te
            let t = this.EmitCon env c
            let addr = declareGlobal (getGlobalName id) t theModule
            buildStore value addr builder |> ignore
            this.RestoreBlock parent
            // TODO migrate to TryAdd for dotnet core 3.0
            if not (env.named_refs.ContainsKey(id)) then
                env.named_refs.Add(id, addr)
        | _ ->
            this.EmitStmt env s

    member private this.EmitMainPrologue(env : Env.env) =
        let parent = this.SwitchBlock mainBlock
        buildRet (constInt 0) builder |> ignore
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
    let context = createContext()
    let mdl = createModule context "punkage"
    new Emitter(mdl, context)
