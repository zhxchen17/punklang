
structure CheckDirect :> CHECK_DIRECT =
   struct

      open ILDirect
      open SubstDirect
      open ContextDirect
      open EquivDirect

      exception TypeError = Misc.TypeError

      fun checkKind ctx k =
         (case k of
             Ktype => ()

           | Ksing c =>
                checkCon ctx c Ktype

           | Kpi (k1, k2) =>
                (
                checkKind ctx k1;
                checkKind (extendKind ctx k1) k2
                )

           | Ksigma (k1, k2) =>
                (
                checkKind ctx k1;
                checkKind (extendKind ctx k1) k2
                )

           | Kunit => ())

      and inferCon ctx c =
         (case c of
             Cvar (i, _) =>
                selfify c (lookupKind ctx i)

           | Clam (k, c) =>
                (
                checkKind ctx k;
                Kpi (k, inferCon (extendKind ctx k) c)
                )

           | Capp (c1, c2) =>
                (case inferCon ctx c1 of
                    Kpi (dom, cod) =>
                       (
                       checkCon ctx c2 dom;
                       substKind c2 cod
                       )
                  | _ =>
                       raise TypeError)

           | Cpair (c1, c2) =>
                Ksigma (inferCon ctx c1, liftKind 1 (inferCon ctx c2))

           | Cpi1 c' =>
                (case inferCon ctx c' of
                    Ksigma (k1, k2) =>
                       k1
                  | _ =>
                       raise TypeError)

           | Cpi2 c' =>
                (case inferCon ctx c' of
                    Ksigma (k1, k2) =>
                       substKind (Cpi1 c') k2
                  | _ =>
                       raise TypeError)

           | Cunit => Kunit

           | Carrow (c1, c2) =>
                (
                checkCon ctx c1 Ktype;
                checkCon ctx c2 Ktype;
                Ksing c
                )

           | Cforall (k, c') =>
                (
                checkKind ctx k;
                checkCon (extendKind ctx k) c' Ktype;
                Ksing c
                )

           | Cexists (k, c') =>
                (
                checkKind ctx k;
                checkCon (extendKind ctx k) c' Ktype;
                Ksing c
                )

           | Cprod cl =>
                (
                List.app (fn c' => checkCon ctx c' Ktype) cl;
                Ksing c
                )

           | Csum cl =>
                (
                List.app (fn c' => checkCon ctx c' Ktype) cl;
                Ksing c
                )

           | Crec c' =>
                (
                checkCon (extendKind ctx Ktype) c' Ktype;
                Ksing c
                )

           | Ctag c' =>
                (
                checkCon ctx c' Ktype;
                Ksing c
                )

           | Cref c' =>
                (
                checkCon ctx c' Ktype;
                Ksing c
                )

           | Cexn => Ksing Cexn
           | Cbool => Ksing Cbool
           | Cint => Ksing Cint
           | Cchar => Ksing Cchar
           | Cstring => Ksing Cstring)

      and checkCon ctx c k =
         subkind ctx (inferCon ctx c) k

      fun whnfAnnot ctx t =
         (
         checkCon ctx t Ktype;
         whnf ctx t
         )

      structure PrimType =
         PrimTypeFun (structure Param =
                         struct
                            open ILDirect
                            val Cunittype = Cprod []
                         end)

      fun inferTerm ctx e =
         (case e of
             Tvar v =>
                lookupType ctx v

           | Tlam (v, dom, e') =>
                (
                checkCon ctx dom Ktype;
                Carrow (dom, inferTerm (extendType ctx v dom) e')
                )

           | Tapp (e1, e2) =>
                (case inferTermWhnf ctx e1 of
                    Carrow (dom, cod) =>
                       (
                       checkTerm ctx e2 dom;
                       cod
                       )
                  | _ =>
                       raise TypeError)

           | Tplam (k, e') =>
                (
                checkKind ctx k;
                Cforall (k, inferTerm (extendKind ctx k) e')
                )

           | Tpapp (e', c) =>
                (case inferTermWhnf ctx e' of
                    Cforall (k, t) =>
                       (
                       checkCon ctx c k;
                       substCon c t
                       )
                  | _ =>
                       raise TypeError)

           | Tpack (c, e', annot) =>
                (case whnfAnnot ctx annot of
                    Cexists (k, t) =>
                       (
                       checkCon ctx c k;
                       checkTerm ctx e' (substCon c t);
                       annot
                       )
                  | _ =>
                       raise TypeError)

           | Tunpack (v, e1, e2) =>
                (case inferTermWhnf ctx e1 of
                    Cexists (k1, t1) =>
                       let
                          val ctx' = extendType (extendKind ctx k1) v t1
                          val t2 = inferTerm ctx' e2
                          val t2' = substCon (inhabitant k1) t2
                       in
                          equiv ctx' t2 (liftCon 1 t2') Ktype;
                          t2'
                       end
                  | _ =>
                       raise TypeError)

           | Ttuple el =>
                Cprod (map (inferTerm ctx) el)

           | Tproj (e', i) =>
                (case inferTermWhnf ctx e' of
                    Cprod tl =>
                       (List.nth (tl, i)
                        handle Subscript => raise TypeError)
                  | _ =>
                       raise TypeError)

           | Tinj (e', i, annot) =>
                (case whnfAnnot ctx annot of
                    Csum tl =>
                       let
                          val t =
                             List.nth (tl, i)
                             handle Subscript => raise TypeError
                       in
                          checkTerm ctx e' t;
                          annot
                       end
                  | _ =>
                       raise TypeError)

           | Tcase (e', []) =>
                raise TypeError

           | Tcase (e', (v1, e1) :: rest) =>
                (case inferTermWhnf ctx e' of
                    Csum tl =>
                       (case tl of
                           [] =>
                              raise TypeError
                         | t1 :: trest =>
                              let
                                 val t = inferTerm (extendType ctx v1 t1) e1
                              in
                                 (ListPair.appEq
                                     (fn ((vi, ei), ti) =>
                                         checkTerm (extendType ctx vi ti) ei t)
                                     (rest, trest)
                                  handle ListPair.UnequalLengths => raise TypeError);
                                 t
                              end)
                  | _ =>
                       raise TypeError)

           | Troll (e', annot) =>
                (case whnfAnnot ctx annot of
                    Crec t =>
                       (
                       checkTerm ctx e' (substCon annot t);
                       annot
                       )
                  | _ =>
                       raise TypeError)

           | Tunroll e' =>
                (case inferTermWhnf ctx e' of
                    t as Crec t' =>
                       substCon t t'
                  | _ =>
                       raise TypeError)

           | Ttag (e1, e2) =>
                (case inferTermWhnf ctx e1 of
                    Ctag t =>
                       (
                       checkTerm ctx e2 t;
                       Cexn
                       )
                  | _ =>
                       raise TypeError)
                                 
           | Tiftag (e1, e2, v, e3, e4) =>
                (case inferTermWhnf ctx e1 of
                    Ctag t =>
                       let
                          val () = checkTerm ctx e2 Cexn
                          val t' = inferTerm (extendType ctx v t) e3
                       in
                          checkTerm ctx e4 t';
                          t'
                       end
                  | _ =>
                       raise TypeError)

           | Tnewtag t =>
                (
                checkCon ctx t Ktype;
                Ctag t
                )

           | Traise (e', t) =>
                (
                checkTerm ctx e' Cexn;
                checkCon ctx t Ktype;
                t
                )

           | Thandle (e1, v, e2) =>
                let
                   val t = inferTerm ctx e1
                in
                   checkTerm (extendType ctx v Cexn) e2 t;
                   t
                end

           | Tref e' =>
                Cref (inferTerm ctx e')

           | Tderef e' =>
                (case inferTermWhnf ctx e' of
                    Cref t =>
                       t
                  | _ =>
                       raise TypeError)

           | Tassign (e1, e2) =>
                (case inferTermWhnf ctx e1 of
                    Cref t =>
                       (
                       checkTerm ctx e2 t;
                       Cprod []
                       )
                  | _ =>
                       raise TypeError)

           | Tbool b => Cbool

           | Tif (e1, e2, e3) =>
                let
                   val () = checkTerm ctx e1 Cbool
                   val t = inferTerm ctx e2
                in
                   checkTerm ctx e3 t;
                   t
                end

           | Tint _ => Cint
           | Tchar _ => Cchar
           | Tstring _ => Cstring

           | Tlet (v, e1, e2) =>
                let
                   val t = inferTerm ctx e1
                in
                   inferTerm (extendType ctx v t) e2
                end

           | Tprim (prim, el) =>
                let
                   val (tl, t) = PrimType.primtype prim
                in
                   (ListPair.appEq
                       (fn (ei, ti) => checkTerm ctx ei ti)
                       (el, tl)
                    handle ListPair.UnequalLengths => raise TypeError);
                   t
                end)

      and inferTermWhnf ctx e =
         whnf ctx (inferTerm ctx e)

      and checkTerm ctx e t =
         equiv ctx (inferTerm ctx e) t Ktype



      fun checkProgram t e =
         checkTerm empty e t

   end
