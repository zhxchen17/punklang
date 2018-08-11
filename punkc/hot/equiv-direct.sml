
structure EquivDirect :> EQUIV_DIRECT =
   struct

      open ILDirect
      open SubstDirect
      open ContextDirect

      exception TypeError = Misc.TypeError

      fun naturalKind ctx c =
         (case c of
             Cvar (i, _) =>
                lookupKind ctx i
           | Capp (c1, c2) =>
                (case naturalKind ctx c1 of
                    Kpi (k1, k2) =>
                       substKind c2 k2
                  | _ =>
                       raise TypeError)
           | Cpi1 c' =>
                (case naturalKind ctx c' of
                    Ksigma (k1, k2) => k1
                  | _ =>
                       raise TypeError)
           | Cpi2 c' =>
                (case naturalKind ctx c' of
                    Ksigma (k1, k2) =>
                       substKind (Cpi1 c') k2
                  | _ =>
                       raise TypeError)
           | Carrow _ => Ktype
           | Cforall _ => Ktype
           | Cexists _ => Ktype
           | Cprod _ => Ktype
           | Csum _ => Ktype
           | Crec _ => Ktype
           | Ctag _ => Ktype
           | Cref _ => Ktype
           | Cexn => Ktype
           | Cbool => Ktype
           | Cint => Ktype
           | Cchar => Ktype
           | Cstring => Ktype
           | _ =>
                raise TypeError)

      fun whreduce c =
         (case c of
             Capp (c1, c2) =>
                (case whreduce c1 of
                    Clam (_, c1') =>
                       whreduce (substCon c2 c1')
                  | c1' =>
                       Capp (c1', c2))
           | Cpi1 c' =>
                (case whreduce c' of
                    Cpair (c1, c2) =>
                       whreduce c1
                  | c'' =>
                       Cpi1 c'')
           | Cpi2 c' =>
                (case whreduce c' of
                    Cpair (c1, c2) =>
                       whreduce c2
                  | c'' =>
                       Cpi2 c'')
           | _ => c)

      fun whnf ctx c =
         let
            val c' = whreduce c
         in
            (case naturalKind ctx c' of
                Ksing c'' =>
                   whnf ctx c''
              | _ =>
                   c')
         end

      fun equiv ctx c1 c2 k =
         (case k of
             Ktype =>
                (
                equivPath ctx (whnf ctx c1) (whnf ctx c2);
                ()
                )
           | Ksing _ => ()
           | Kpi (k1, k2) =>
                equiv
                   (extendKind ctx k1)
                   (Capp (liftCon 1 c1, Cvar (0, NONE)))
                   (Capp (liftCon 1 c2, Cvar (0, NONE)))
                   k2
           | Ksigma (k1, k2) =>
               (
               equiv ctx (Cpi1 c1) (Cpi1 c2) k1;
               equiv ctx (Cpi2 c1) (Cpi2 c2) (substKind (Cpi1 c1) k2)
               )
           | Kunit => ())

      and equivPath ctx c1 c2 =
         (case (c1, c2) of
             (Cvar (i1, _), Cvar (i2, _)) =>
                if i1 = i2 then
                   lookupKind ctx i1
                else
                   raise TypeError
           | (Capp (c1a, c1b), Capp (c2a, c2b)) =>
                (case equivPath ctx c1a c2a of
                    Kpi (k1, k2) =>
                       (
                       equiv ctx c1b c2b k1;
                       substKind c1b k2
                       )
                  | _ =>
                       raise TypeError)
           | (Cpi1 c1', Cpi1 c2') =>
                (case equivPath ctx c1' c2' of
                    Ksigma (k1, k2) =>
                       k1
                  | _ =>
                       raise TypeError)
           | (Cpi2 c1', Cpi2 c2') =>
                (case equivPath ctx c1' c2' of
                    Ksigma (k1, k2) =>
                       substKind (Cpi1 c1') k2
                  | _ =>
                       raise TypeError)
           | (Carrow (c1a, c1b), Carrow (c2a, c2b)) =>
                (
                equiv ctx c1a c2a Ktype;
                equiv ctx c1b c2b Ktype;
                Ktype
                )
           | (Cforall (k1, c1'), Cforall (k2, c2')) =>
                (
                samekind ctx k1 k2;
                equiv (extendKind ctx k1) c1' c2' Ktype;
                Ktype
                )
           | (Cexists (k1, c1'), Cexists (k2, c2')) =>
                (
                samekind ctx k1 k2;
                equiv (extendKind ctx k1) c1' c2' Ktype;
                Ktype
                )
           | (Cprod cl1, Cprod cl2) =>
                ((
                 ListPair.appEq (fn (c1, c2) => equiv ctx c1 c2 Ktype) (cl1, cl2);
                 Ktype
                 )
                 handle ListPair.UnequalLengths => raise TypeError)
           | (Csum cl1, Csum cl2) =>
                ((
                 ListPair.appEq (fn (c1, c2) => equiv ctx c1 c2 Ktype) (cl1, cl2);
                 Ktype
                 )
                 handle ListPair.UnequalLengths => raise TypeError)
           | (Crec c1', Crec c2') =>
                (
                equiv (extendKind ctx Ktype) c1' c2' Ktype;
                Ktype
                )
           | (Ctag c1', Ctag c2') =>
                (
                equiv ctx c1' c2' Ktype;
                Ktype
                )
           | (Cref c1', Cref c2') =>
                (
                equiv ctx c1' c2' Ktype;
                Ktype
                )
           | (Cexn, Cexn) => Ktype
           | (Cbool, Cbool) => Ktype
           | (Cint, Cint) => Ktype
           | (Cchar, Cchar) => Ktype
           | (Cstring, Cstring) => Ktype
           | _ =>
                raise TypeError)

      and samekind ctx k1 k2 =
         (case (k1, k2) of
             (Ktype, Ktype) => ()
           | (Ksing c1, Ksing c2) =>
                equiv ctx c1 c2 Ktype
           | (Kpi (k1a, k1b), Kpi (k2a, k2b)) =>
                (
                samekind ctx k1a k2a;
                samekind (extendKind ctx k1a) k1b k2b
                )
           | (Ksigma (k1a, k1b), Ksigma (k2a, k2b)) =>
                (
                samekind ctx k1a k2a;
                samekind (extendKind ctx k1a) k1b k2b
                )
           | (Kunit, Kunit) => ()
           | _ =>
                raise TypeError)

      fun subkind ctx k1 k2 =
         (case (k1, k2) of
             (Ktype, Ktype) => ()
           | (Ksing c1, Ksing c2) =>
                equiv ctx c1 c2 Ktype
           | (Ksing _, Ktype) => ()
           | (Kpi (k1a, k1b), Kpi (k2a, k2b)) =>
                (
                subkind ctx k2a k1a;
                subkind (extendKind ctx k2a) k1b k2b
                )
           | (Ksigma (k1a, k1b), Ksigma (k2a, k2b)) =>
                (
                subkind ctx k1a k2a;
                subkind (extendKind ctx k1a) k1b k2b
                )
           | (Kunit, Kunit) => ()
           | _ =>
                raise TypeError)

      fun selfify c k =
         (case k of
             Ktype =>
                Ksing c
           | Ksing _ => k
           | Kpi (k1, k2) =>
                Kpi (k1, selfify (Capp (liftCon 1 c, Cvar (0, NONE))) k2)
           | Ksigma (k1, k2) =>
                Ksigma (selfify (Cpi1 c) k1,
                        liftKind 1 (selfify (Cpi2 c) (substKind (Cpi1 c) k2)))
           | Kunit => k)

      fun inhabitant k =
         (case k of
             Ktype =>
                Cprod []  (* unit *)
           | Ksing c => c
           | Kpi (k1, k2) =>
                Clam (k1, inhabitant k2)
           | Ksigma (k1, k2) =>
                let
                   val c = inhabitant k1
                in
                   Cpair (c, inhabitant (substKind c k2))
                end
           | Kunit => Cunit)

   end
