open Bir
open Ast
open Utils

let new_emitter () =
  let context = create_context () in
  let int_type = integer_type context in
  let byte_type = byte_type context in
  let bool_type = boolean_type context in
  let str_type = pointer_type byte_type in
  let void_type = void_type context in
  let mdl = create_module context "punkage" in

  let entry_block =
    let ft = function_type int_type [int_type] in
    let the_function = declare_function "main" ft mdl in
    append_block context "entry" the_function in

  let declare_printf mdl =
    let ft = var_arg_function_type int_type [ pointer_type byte_type ] in
    declare_function "printf" ft mdl in

  let declare_exit mdl =
    let ft = function_type void_type [ int_type ] in
    declare_function "exit" ft mdl in

  object (self)
    val mutable the_module = mdl
    val mutable main_block = entry_block
    val mutable builder = make_builder context
    val mutable current_block = entry_block

    method private get_addr env ((_, lv) as tlv) =
      let { Env.named_values; } = env in
      match lv with
      | Evar (i, _) -> Hashtbl.find named_values i
      | Efield (b, (i, Some f)) ->
        let base = self#get_addr env b in
        assert (i >= 0);
        build_struct_gep base i f builder
      | _ -> self#emit_texp env tlv

    method private switch_block blk =
      let ret = current_block in
      current_block <- blk;
      position_at_end blk builder;
      ret

    method private restore_block blk =
      current_block <- blk;
      position_at_end blk builder

    method private emit_func env name (vmcl, cr, body) =
      let fname =
        match name with
        | Some s -> s
        | None -> Env.new_func_name () in
      begin
        let { Env.named_values; } = env in
        let ft =
          function_type
            (self#emit_con env cr)
            (List.map (fun (v, _, c) -> self#emit_con env c) vmcl) in
        let the_function =
          declare_function fname ft the_module in
        let set_param i a =
          match (Array.of_list vmcl).(i) with
          | ((id, Some n), _, c) ->
            set_param_name n a;
            Hashtbl.add named_values id a;
          | _ -> raise (Error "unnamed param") in
        Array.iteri set_param (params the_function);
        (* Create a new basic block to start insertion into. *)
        let block = append_block context "entry" the_function in
        let parent = self#switch_block block in
        let _ = self#emit_stmt env body in
        ignore (build_ret (undef (self#emit_con env cr)) builder);
        (* Validate the generated code, checking for consistency. *)
        (* Llvm_analysis.assert_valid_function the_function; *)
        self#restore_block parent;
        the_function
      end

    method emit_con env c =
      match c with
      | Cint -> int_type
      | Cbool -> bool_type
      | Cstring -> str_type
      | Cnamed (v, c) -> self#emit_con env c
      | Carray (c, _) -> pointer_type (self#emit_con env c)
      | Cprod (cl, _) ->
        struct_type context (List.map (self#emit_con env) cl)
      | Carrow (cl, cr) -> function_type (self#emit_con env cr)
                             (List.map (self#emit_con env) cl)
      | _ -> raise (Fatal ("unimplemented type emission " ^ (string_of_con c)))

    method emit_texp env (c, e) =
      let { Env.named_values; } = env in
      match e with
      | Evar (id, n) when id >= 0 -> begin
        try
        let v = Hashtbl.find named_values id in
        if Hashtbl.mem env.Env.persistent_set id then
          build_load v ((Env.mangle_name id) ^ "_ld") builder
        else
          v
        with e ->
          Option.value_map n ~default:() ~f:print_string;
          raise e
      end
      | Evar (id, _) when id < 0 ->
        raise (Error "unknown variable name")
      | Eint i -> const_int i
      | Estring s ->
        build_global_stringptr s "string_tmp" builder
      | Ebool b ->
        if b then const_bool true else const_bool false
      | Eop (o, el) ->
        begin match o with
          | Add ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            build_add lhs rhs builder
          | Multiply ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            build_mul lhs rhs builder
          | Minus ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            build_sub lhs rhs builder
          | Equal ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            build_icmp Icmp_eq lhs rhs builder
          | Cprintf ->
            let vl = List.map (self#emit_texp env) el in
            begin match lookup_function "printf" the_module with
              | None -> raise (Fatal "printf should be declared")
              | Some printer ->
                build_call printer (Array.of_list vl) "unit" builder
            end
          | Lt ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            build_icmp Icmp_slt lhs rhs builder
          | Idx ->
            let lhs = self#emit_texp env (List.nth el 0) in
            let rhs = self#emit_texp env (List.nth el 1) in
            let p = build_gep lhs [ rhs ] "idx" builder in
            build_load p "ld" builder
        end
      | Efunc (vmcl, cr, body) ->
        self#emit_func env None (vmcl, cr, body)
      | Efield (b, (i, Some f)) ->
        assert (i >= 0);
        build_extractvalue (self#emit_texp env b) i f builder
      | Earray (c, el) ->
        let res = build_array_alloca
          (self#emit_con env c)
          (const_int (List.length el))
          "array_cns" builder in
        let init_elem i e' =
          let gep =
            build_gep res [ const_int i ] "gep" builder in
          let _ = build_store (self#emit_texp env e') gep builder in
          () in
        List.iteri init_elem el;
        res
      | Econ (Cnamed ((_, Some s), Cprod (cl, _))) ->
        let ty = named_struct_type context s the_module in
        let _ =
          struct_set_body ty (List.map (self#emit_con env) cl) false in
        const_nil ()
      | Ector (Cnamed ((_, Some s), _), sel) ->
        begin match type_by_name s the_module with
          | None -> raise (Error "type not found")
          | Some ty ->
            let elems = struct_element_types ty in
            let start = const_struct context (Array.map undef elems) in
            let (_, res) = List.fold_left
              (fun (i, v) e ->
                 (i + 1,
                  build_insertvalue v (self#emit_texp env e) i "field" builder))
              (0, start) (List.map snd sel) in
            res
        end
      | Eapp (f, params) ->
        build_call (self#emit_texp env f)
          (Array.of_list (List.map (self#emit_texp env) params)) "res" builder
      | _ -> raise (Fatal ("expr code emission unimplemented yet" ^ (string_of_exp e)))

    method emit_stmt env s =
      let { Env.named_values; } = env in
      match s with
      | Sret te ->
        let ret = self#emit_texp env te in
        ignore (build_ret ret builder);
      | Sdecl ((id, n), m, ((c, _) as te)) ->
        let c' = self#emit_con env c in
        if env.is_top then begin
          let env' = { env with is_top = false; } in
          match te with
          | (_, Efunc (vmcl, cr, body)) ->
            let func_name = Env.mangle_func_name id in
            ignore (self#emit_func env' (Some func_name) (vmcl, cr, body));
          | (_, Econ _) ->
            let value = self#emit_texp env' te in
            ignore (define_global (Env.mangle_name id)
                      Bir_unit_type value the_module);
          | _ ->
            Hashtbl.add env.persistent_set id ();
            let addr = define_global (Env.mangle_name id) c' (undef c')
                the_module in
            let value = self#emit_texp env' te in
            Hashtbl.add named_values id addr;
            let parent = self#switch_block main_block in
            ignore (build_store value addr builder);
            self#restore_block parent;
        end else begin
          let value = self#emit_texp env te in
          Hashtbl.add env.persistent_set id ();
          let addr =
            build_alloca
              (self#emit_con env c) (Env.mangle_name id) builder in
          ignore (build_store value addr builder);
          Hashtbl.add named_values id addr;
        end
      | Sblk sl ->
        if env.is_top then begin
          let _ = declare_exit the_module in
          let _ = declare_printf the_module in
          let update_global env s =
            match s with
            | Sdecl ((id, _), _, (c, Efunc _)) ->
              let c' = self#emit_con env c in
              let func = declare_function (Env.mangle_func_name id)
                   c' the_module in
              Hashtbl.add env.persistent_set id ();
              let addr = define_global (Env.mangle_name id)
                  c' func the_module in
              Hashtbl.add named_values id addr;
            | _ -> () in
          List.iter (update_global env) sl;
          List.iter (self#emit_stmt env) sl;
          let _ = build_ret (const_int 0) builder in
          ()
        end else
          List.iter (self#emit_stmt env) sl;
      | Sexpr te ->
        let _ = self#emit_texp env te in ()
      | Sasgn (lval, te) ->
        ignore
          (build_store (self#emit_texp env te)
             (self#get_addr env lval) builder);
      | Sif (te, s0, s1) ->
        let pred = self#emit_texp env te in
        (* Grab the first block so that we might later add the conditional
         * branch to it at the end of the function. *)
        let start_bb = insertion_block builder in
        let the_function = block_parent start_bb in

        let then_bb = append_block context "then" the_function in

        (* Emit 'then' value. *)
        position_at_end then_bb builder;
        self#emit_stmt env s0;

        (* Codegen of 'then' can change the current block, update then_bb for
         * the phi. We create a new name because one is used for the phi node,
         * and the other is used for the conditional branch. *)
        let new_then_bb = insertion_block builder in

        (* Emit 'else' value. *)
        let else_bb = append_block context "else" the_function in
        position_at_end else_bb builder;
        self#emit_stmt env s1;

        (* Codegen of 'else' can change the current block, update else_bb for
         * the phi. *)
        let new_else_bb = insertion_block builder in

        (* Emit merge block. *)
        let merge_bb = append_block context "cont" the_function in

        (* Return to the start block to add the conditional branch. *)
        position_at_end start_bb builder;
        ignore (build_cond_br pred then_bb else_bb builder);

        (* Set a unconditional branch at the end of the 'then' block and the
         * 'else' block to the 'merge' block. *)
        position_at_end new_then_bb builder; ignore (build_br merge_bb builder);
        position_at_end new_else_bb builder; ignore (build_br merge_bb builder);

        (* Finally, set the builder to the end of the merge block. *)
        position_at_end merge_bb builder;

      | Swhile (e, s) ->

        let start_bb = insertion_block builder in
        let the_function = block_parent start_bb in

        let cond_bb = append_block context "cond" the_function in

        position_at_end cond_bb builder;
        let pred = self#emit_texp env e in

        let new_cond_bb = insertion_block builder in

        let loop_bb = append_block context "loop" the_function in
        position_at_end loop_bb builder;
        self#emit_stmt env s;

        let new_loop_bb = insertion_block builder in

        (* Emit merge block. *)
        let merge_bb = append_block context "cont" the_function in

        position_at_end start_bb builder;
        ignore (build_br cond_bb builder);

        position_at_end new_cond_bb builder;
        ignore (build_cond_br pred loop_bb merge_bb builder);

        position_at_end new_loop_bb builder;
        ignore (build_br new_cond_bb builder);

        position_at_end merge_bb builder;

    method get_module () = the_module
  end
