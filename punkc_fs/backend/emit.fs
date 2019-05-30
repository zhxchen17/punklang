module Emit

module Hashtbl = FSharp.Compatibility.OCaml.Hashtbl
module Array = FSharp.Compatibility.OCaml.Array

open Bir
open ir.Ast
open Errors

let value_map x d f =
    match x with
    | Some x' -> f x'
    | None -> d

type Emitter(mdl, context) =
    let int_type = integer_type context
    let byte_type = byte_type context
    let bool_type = boolean_type context
    let str_type = pointer_type byte_type
    let void_type = void_type context

    let entry_block =
        let ft = function_type int_type [ int_type ]
        let the_function = declare_function "main" ft mdl
        append_block context "entry" the_function

    let mutable the_module = mdl
    let mutable main_block = entry_block
    let mutable builder = make_builder context
    let mutable current_block = entry_block

    let declare_printf mdl =
        let ft = var_arg_function_type int_type [ pointer_type byte_type ]
        declare_function "printf" ft mdl

    let declare_exit mdl =
        let ft = function_type void_type [ int_type ]
        declare_function "exit" ft mdl

    member private this.get_addr (env : Env.env) ((_, lv) as tlv) =
        let named_values = env.named_values
        match lv with
        | Evar(i, _) -> Hashtbl.find named_values i
        | Efield(b, (i, Some f)) ->
            let b = this.get_addr env b
            assert (i >= 0)
            build_struct_gep b i f builder
        | _ -> this.emit_texp env tlv

    member private this.switch_block blk =
        let ret = current_block
        current_block <- blk
        position_at_end blk builder
        ret

    member private this.restore_block blk =
        current_block <- blk
        position_at_end blk builder

    member private this.emit_func (env : Env.env) name (vmcl, cr, body) =
        let fname =
            match name with
            | Some s -> s
            | None -> Env.new_func_name()
        (let named_values = env.named_values
         let ft =
             function_type (this.emit_con env cr)
                 (List.map (fun (v, _, c) -> this.emit_con env c) vmcl)
         let the_function = declare_function fname ft the_module

         let set_param i a =
             match (Array.of_list vmcl).[i] with
             | ((id, Some n), _, c) ->
                 set_param_name n a
                 Hashtbl.add named_values id a
             | _ -> raise (BackendError "unnamed param")
         Array.iteri set_param (``params`` the_function)
         (* Create a new basic block to start insertion into. *)
         let block = append_block context "entry" the_function
         let parent = this.switch_block block
         let _ = this.emit_stmt env body
         ignore (build_ret (undef (this.emit_con env cr)) builder)
         (* Validate the generated code, checking for consistency. *)
         (* Llvm_analysis.assert_valid_function the_function; *)
         this.restore_block parent
         the_function)

    member this.emit_con env c =
        match c with
        | Cint -> int_type
        | Cbool -> bool_type
        | Cstring -> str_type
        | Cnamed(v, c) -> this.emit_con env c
        | Carray c -> pointer_type (this.emit_con env c)
        | Cprod(cl, _) -> struct_type context (List.map (this.emit_con env) cl)
        | Carrow(cl, cr) ->
            function_type (this.emit_con env cr)
                (List.map (this.emit_con env) cl)
        | _ -> raise (BackendFatal("unimplemented type emission " ^ (string c)))

    member this.emit_texp (env : Env.env) (c, e) =
        let named_values = env.named_values
        match e with
        | Evar(id, n) when id >= 0 ->
            try
                let v = Hashtbl.find named_values id
                if Hashtbl.mem env.persistent_set id then
                    build_load v ((Env.mangle_name id) ^ "_ld") builder
                else v
            with e ->
                value_map n () (printf "%s")
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
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 build_add lhs rhs builder
             | Multiply ->
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 build_mul lhs rhs builder
             | Minus ->
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 build_sub lhs rhs builder
             | Equal ->
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 build_icmp Icmp_eq lhs rhs builder
             | Cprintf ->
                 let vl = List.map (this.emit_texp env) el
                 (match lookup_function "printf" the_module with
                  | None -> raise (BackendFatal "printf should be declared")
                  | Some printer ->
                      build_call printer (Array.of_list vl) "unit" builder)
             | Lt ->
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 build_icmp Icmp_slt lhs rhs builder
             | Idx ->
                 let lhs = this.emit_texp env (List.nth el 0)
                 let rhs = this.emit_texp env (List.nth el 1)
                 let p = build_gep lhs [ rhs ] "idx" builder
                 build_load p "ld" builder)
        | Efunc(vmcl, cr, body) -> this.emit_func env None (vmcl, cr, body)
        | Efield(b, (i, Some f)) ->
            assert (i >= 0)
            build_extractvalue (this.emit_texp env b) i f builder
        | Earray(c, el) ->
            let c' = this.emit_con env c
            let l = const_int (List.length el)
            let res = build_array_alloca c' l "array_cns" builder

            let init_elem i e' =
                let gep = build_gep res [ const_int i ] "gep" builder
                let _ = build_store (this.emit_texp env e') gep builder
                ()
            List.iteri init_elem el
            res
        | Econ(Cnamed((_, Some s), Cprod(cl, _))) ->
            let ty = named_struct_type context s the_module
            let _ = struct_set_body ty (List.map (this.emit_con env) cl) false
            const_nil()
        | Ector(Cnamed((_, Some s), _), sel) ->
            (match type_by_name s the_module with
             | None -> raise (BackendError "type not found")
             | Some ty ->
                 let elems = struct_element_types ty
                 let start = const_struct context (Array.map undef elems)
                 let roll =
                     (fun (i, v) e ->
                     (i + 1,
                      build_insertvalue v (this.emit_texp env e) i "field"
                          builder))
                 let (_, res) = List.fold roll (0, start) (List.map snd sel)
                 res)
        | Eapp(f, ``params``) ->
            build_call (this.emit_texp env f)
                (Array.of_list (List.map (this.emit_texp env) ``params``)) "res"
                builder
        | _ ->
            raise
                (BackendFatal("expr code emission unimplemented" ^ (string e)))

    member this.emit_stmt env s =
        let named_values = env.named_values
        match s with
        | Sret te ->
            let ret = this.emit_texp env te
            ignore (build_ret ret builder)
        | Sdecl((id, n), m, ((c, _) as te)) ->
            let c' = this.emit_con env c
            if env.is_top then
                (let env' = { env with is_top = false }
                 match te with
                 | (_, Efunc(vmcl, cr, body)) ->
                     let func_name = Env.mangle_func_name id
                     ignore
                         (this.emit_func env' (Some func_name) (vmcl, cr, body))
                 | (_, Econ _) ->
                     let value = this.emit_texp env' te
                     ignore
                         (define_global (Env.mangle_name id) Bir_unit_type value
                              the_module)
                 | _ ->
                     Hashtbl.add env.persistent_set id ()
                     let id' = Env.mangle_name id
                     let addr = define_global id' c' (undef c') the_module
                     let value = this.emit_texp env' te
                     Hashtbl.add named_values id addr
                     let parent = this.switch_block main_block
                     ignore (build_store value addr builder)
                     this.restore_block parent)
            else
                (let value = this.emit_texp env te
                 Hashtbl.add env.persistent_set id ()
                 let addr =
                     build_alloca (this.emit_con env c) (Env.mangle_name id)
                         builder
                 ignore (build_store value addr builder)
                 Hashtbl.add named_values id addr)
        | Sblk sl ->
            if env.is_top then
                (let _ = declare_exit the_module
                 let _ = declare_printf the_module

                 let update_global env s =
                     match s with
                     | Sdecl((id, _), _, (c, Efunc _)) ->
                         let c' = this.emit_con env c
                         let fid' = Env.mangle_func_name id
                         let func = declare_function fid' c' the_module
                         Hashtbl.add env.persistent_set id ()
                         let id' = Env.mangle_name id
                         let addr = define_global id' c' func the_module
                         Hashtbl.add named_values id addr
                     | _ -> ()
                 List.iter (update_global env) sl
                 List.iter (this.emit_stmt env) sl
                 let _ = build_ret (const_int 0) builder
                 ())
            else List.iter (this.emit_stmt env) sl
        | Sexpr te ->
            let _ = this.emit_texp env te in ()
        | Sasgn(lval, te) ->
            ignore
                (build_store (this.emit_texp env te) (this.get_addr env lval)
                     builder)
        | Sif(te, s0, s1) ->
            let pred = this.emit_texp env te
            (* Grab the first block so that we might later add the conditional
         * branch to it at the end of the function. *)
            let start_bb = insertion_block builder
            let the_function = block_parent start_bb
            let then_bb = append_block context "then" the_function
            (* Emit 'then' value. *)
            position_at_end then_bb builder
            this.emit_stmt env s0
            (* Codegen of 'then' can change the current block, update then_bb for
         * the phi. We create a new name because one is used for the phi node,
         * and the other is used for the conditional branch. *)
            let new_then_bb = insertion_block builder
            (* Emit 'else' value. *)
            let else_bb = append_block context "else" the_function
            position_at_end else_bb builder
            this.emit_stmt env s1
            (* Codegen of 'else' can change the current block, update else_bb for
         * the phi. *)
            let new_else_bb = insertion_block builder
            (* Emit merge block. *)
            let merge_bb = append_block context "cont" the_function
            (* Return to the start block to add the conditional branch. *)
            position_at_end start_bb builder
            ignore (build_cond_br pred then_bb else_bb builder)
            (* Set a unconditional branch at the end of the 'then' block and the
         * 'else' block to the 'merge' block. *)
            position_at_end new_then_bb builder
            ignore (build_br merge_bb builder)
            position_at_end new_else_bb builder
            ignore (build_br merge_bb builder)
            (* Finally, set the builder to the end of the merge block. *)
            position_at_end merge_bb builder
        | Swhile(e, s) ->
            let start_bb = insertion_block builder
            let the_function = block_parent start_bb
            let cond_bb = append_block context "cond" the_function
            position_at_end cond_bb builder
            let pred = this.emit_texp env e
            let new_cond_bb = insertion_block builder
            let loop_bb = append_block context "loop" the_function
            position_at_end loop_bb builder
            this.emit_stmt env s
            let new_loop_bb = insertion_block builder
            (* Emit merge block. *)
            let merge_bb = append_block context "cont" the_function
            position_at_end start_bb builder
            ignore (build_br cond_bb builder)
            position_at_end new_cond_bb builder
            ignore (build_cond_br pred loop_bb merge_bb builder)
            position_at_end new_loop_bb builder
            ignore (build_br new_cond_bb builder)
            position_at_end merge_bb builder

    member this.get_module() = the_module

let new_emitter() =
    let context = create_context()
    let mdl = create_module context "punkage"
    new Emitter(mdl, context)
