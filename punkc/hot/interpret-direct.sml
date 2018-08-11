
structure InterpretDirect :> INTERPRET_DIRECT =
   struct

      open ILDirect
      open ResultDirect

      structure D = VariableDict

      type env = result D.dict

      structure PrimEval =
         PrimEvalFun
         (structure Param =
             struct
                open ResultDirect

                val Runit = Rtuple []

                fun destRbool k =
                    (case k of
                        Rbool x => SOME x
                      | _ => NONE)
          
                fun destRint k =
                    (case k of
                        Rint x => SOME x
                      | _ => NONE)
          
                fun destRchar k =
                    (case k of
                        Rchar x => SOME x
                      | _ => NONE)
          
                fun destRstring k =
                    (case k of
                        Rstring x => SOME x
                      | _ => NONE)
             end)

      fun eval env e =
         (case e of
             Tvar v =>
                (case D.find env v of
                    SOME r => r
                  | NONE =>
                       raise Wrong)

           | Tlam (v, _, e') =>
                Rfn (fn r => eval (D.insert env v r) e')

           | Tapp (e1, e2) =>
                (case eval env e1 of
                    Rfn f =>
                       f (eval env e2)
                  | _ =>
                       raise Wrong)

           | Tplam (_, e') =>
                Rpfn (fn () => eval env e')

           | Tpapp (e', _) =>
                (case eval env e' of
                    Rpfn f =>
                       f ()
                  | _ =>
                       raise Wrong)

           | Tpack (_, e', _) =>
                Rpack (eval env e')

           | Tunpack (v, e1, e2) =>
                (case eval env e1 of
                    Rpack r =>
                       eval (D.insert env v r) e2
                  | _ =>
                       raise Wrong)

           | Ttuple el =>
                Rtuple (map (eval env) el)

           | Tproj (e', i) =>
                (case eval env e' of
                    Rtuple rl =>
                       (List.nth (rl, i)
                        handle Subscript => raise Wrong)
                  | _ =>
                       raise Wrong)

           | Tinj (e', i, _) =>
                Rinj (eval env e', i)

           | Tcase (e', arms) =>
                (case eval env e' of
                    Rinj (r, i) =>
                       let
                          val (vi, ei) =
                             List.nth (arms, i)
                             handle Subscript => raise Wrong
                       in
                          eval (D.insert env vi r) ei
                       end
                  | _ =>
                       raise Wrong)

           | Troll (e', _) =>
                Rroll (eval env e')

           | Tunroll e' =>
                (case eval env e' of
                    Rroll r => r
                  | _ =>
                       raise Wrong)

           | Ttag (e1, e2) =>
                (case eval env e1 of
                    Rtag tag =>
                       Rexn (tag, eval env e2)
                  | _ =>
                       raise Wrong)

           | Tiftag (e1, e2, v, e3, e4) =>
                (case (eval env e1, eval env e2) of
                    (Rtag tag, Rexn (tag', r)) =>
                       if tag = tag' then
                          eval (D.insert env v r) e3
                       else
                          eval env e4
                  | _ =>
                       raise Wrong)
                       
           | Tnewtag _ =>
                Rtag (ref ())

           | Traise (e', _) =>
                raise (RaiseExn (eval env e'))

           | Thandle (e1, v, e2) =>
                (eval env e1
                 handle RaiseExn r =>
                    eval (D.insert env v r) e2)

           | Tref e' =>
                Rref (ref (eval env e'))

           | Tderef e' =>
                (case eval env e' of
                    Rref (ref r) => r
                  | _ =>
                       raise Wrong)

           | Tassign (e1, e2) =>
                (case eval env e1 of
                    Rref rr =>
                       (
                       rr := eval env e2;
                       Rtuple []
                       )
                  | _ =>
                       raise Wrong)

           | Tbool b =>
                Rbool b

           | Tif (e1, e2, e3) =>
                (case eval env e1 of
                    Rbool true =>
                       eval env e2
                  | Rbool false =>
                       eval env e3
                  | _ =>
                       raise Wrong)

           | Tint i =>
                Rint i

           | Tchar ch =>
                Rchar ch

           | Tstring str =>
                Rstring str

           | Tlet (v, e1, e2) =>
                eval (D.insert env v (eval env e1)) e2

           | Tprim (prim, el) =>
                PrimEval.primeval prim (map (eval env) el))

   end
