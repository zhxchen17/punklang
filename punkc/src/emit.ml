open Llvm
open Ast
open Utils

let new_emitter () =
  let context = global_context () in
  let int_type = integer_type context 32 in
  let void_type = void_type context in
  let mdl = create_module context "punkage" in

  let declare_entry mdl =
    let ft = function_type int_type (Array.make 0 int_type) in
    let the_function = declare_function "main" ft mdl in
    append_block context "entry" the_function in

  let declare_exit mdl =
    let ft = function_type void_type (Array.make 1 int_type) in
    declare_function "exit" ft mdl in

  object (self)
    val mutable the_module = mdl
    val mutable main_block = declare_entry mdl
    val mutable named_values:(int, llvalue) Hashtbl.t
      = Hashtbl.create table_size
    val mutable builder = builder context

    method emit_con env c =
      match c with
      | Cint -> int_type
      | _ -> raise (Fatal "unimplemented type emission")

    method emit_expr env e =
      match e with
      | Evar (id, _) when id >= 0 ->
        let v = Hashtbl.find named_values id in
        if Hashtbl.mem env.Env.persistent_set id then
          build_load v ((Env.mangle_name id) ^ "_ld") builder
        else
          v
      | Evar (id, _) when id < 0 ->
        raise (Error "unknown variable name")
      | Eint i -> const_int int_type i
      | Eop (o, el) ->
        begin match o with
          | Add ->
            let lhs = self#emit_expr env (List.nth el 0) in
            let rhs = self#emit_expr env (List.nth el 1) in
            build_add lhs rhs "add_op" builder
        end
      | Efunc (vcl, cr, body) ->
        begin
          let env = { env with Env.is_top = false } in
          let ft =
            function_type
              (self#emit_con env cr)
              (Array.map
                 (fun (v, c) -> self#emit_con env c)
                 (Array.of_list vcl)) in
          let the_function =
            declare_function (Env.new_func_name ()) ft the_module in
          let set_param i a =
            match (Array.of_list vcl).(i) with
            | ((id, Some n), c) ->
              set_value_name n a;
              Hashtbl.add named_values id a;
            | _ -> raise (Error "unnamed param") in
          Array.iteri set_param (params the_function);
          (* Create a new basic block to start insertion into. *)
          let block = append_block context "entry" the_function in
          position_at_end block builder;
          try
            let _ = self#emit_stmt env body in
            (* Validate the generated code, checking for consistency. *)
            Llvm_analysis.assert_valid_function the_function;
            the_function
          with e ->
            delete_function the_function;
            raise (Error "unable to generate function")
        end
      | Earray (Some c, el) ->
        let res = build_array_alloca
          (self#emit_con env c)
          (const_int int_type (List.length el))
          "array_cns" builder in
        let init_elem i e' =
          let gep =
            build_gep res
              (Array.make 1 (const_int int_type i)) "gep" builder in
          let _ = build_store (self#emit_expr env e') gep builder in
          () in
        List.iteri init_elem el;
        res
      | Econ (Cnamed ((_, Some s), Some (Cprod (cl, _)))) ->
        let ty = named_struct_type context s in
        let _ =
          struct_set_body
            ty (Array.of_list (List.map (self#emit_con env) cl)) false in
        const_null int_type
      | Ector (Cnamed ((_, Some s), _), sel) ->
        begin match type_by_name the_module s with
          | None -> raise (Error "type not found")
          | Some ty ->
            let res = build_alloca ty "struct_tmp" builder in
            List.iteri
              (fun i e ->
                 let gep = build_struct_gep res i "gep" builder in
                 let _ = build_store (self#emit_expr env e) gep builder in
                 ())
              (List.map snd sel);
            res
        end
      | _ -> raise (Fatal "unimplemented")

    method emit_stmt env s =
      match s with
      | Sret e ->
        let ret = self#emit_expr env e in
        let _ = build_ret ret builder in
        ()
      | Sdecl ((id, n), _, e) ->
        let value = self#emit_expr env e in
        let var =
          if env.is_top then begin
            Hashtbl.add env.persistent_set id ();
            define_global (Env.mangle_name id) value the_module
          end else
            value
        in
        Hashtbl.add named_values id var;
      | Sblk sl ->
        List.iter (self#emit_stmt env) sl;
        if env.is_top then begin
          let _ = declare_exit the_module in
          position_at_end main_block builder;
          let _ = build_ret (const_int int_type 0) builder in
          ()
        end else
          ()
      | _ -> ()

    method get_module () = the_module
  end
