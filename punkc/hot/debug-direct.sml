
structure DebugDirect :> DEBUG_DIRECT =
   struct

      open ILDirect

      exception IndexError of int list

      exception IndexErrorKind of kind * int option * int list
      exception IndexErrorCon of con * int option * int list
      exception IndexErrorTerm of term * int option * int list

      val bottom = Depth.bottom
      fun dec path d = Depth.dec (IndexError path) d
      fun join path d1_d2 = Depth.join (IndexError path) d1_d2

      fun mapi f l =
         rev (#1 (foldl (fn (x, (l, i)) => (f (x, i) :: l, i+1)) ([], 0) l))

      fun depthKind path k =
         (case k of
             Ktype => bottom
           | Ksing c =>
                depthCon (0 :: path) c
           | Kpi (k1, k2) =>
                join path (depthKind (0 :: path) k1, dec path (depthKind (1 :: path) k2))
           | Ksigma (k1, k2) =>
                join path (depthKind (0 :: path) k1, dec path (depthKind (1 :: path) k2))
           | Kunit => bottom)

      and depthCon path c =
         (case c of
             Cvar (i, NONE) =>
                Depth.AtLeast i
           | Cvar (i, SOME j) =>
                if i < j then
                   Depth.Exactly j
                else
                   raise (IndexError (rev path))
           | Clam (k, c) =>
                join path (depthKind (0 :: path) k, dec path (depthCon (1 :: path) c))
           | Capp (c1, c2) =>
                join path (depthCon (0 :: path) c1, depthCon (1 :: path) c2)
           | Cpair (c1, c2) =>
                join path (depthCon (0 :: path) c1, depthCon (1 :: path) c2)
           | Cpi1 c =>
                depthCon (0 :: path) c
           | Cpi2 c =>
                depthCon (0 :: path) c
           | Cunit => bottom
           | Carrow (c1, c2) =>
                join path (depthCon (0 :: path) c1, depthCon (1 :: path) c2)
           | Cforall (k, c) =>
                join path (depthKind (0 :: path) k, dec path (depthCon (1 :: path) c))
           | Cexists (k, c) =>
                join path (depthKind (0 :: path) k, dec path (depthCon (1 :: path) c))
           | Cprod cl =>
                #1 (foldl (fn (c, (d, i)) => (join path (depthCon (i :: 0 :: path) c, d), i+1)) (bottom, 0) cl)
           | Csum cl =>
                #1 (foldl (fn (c, (d, i)) => (join path (depthCon (i :: 0 :: path) c, d), i+1)) (bottom, 0) cl)
           | Crec c =>
                dec path (depthCon (0 :: path) c)
           | Ctag c =>
                depthCon (0 :: path) c
           | Cref c =>
                depthCon (0 :: path) c
           | Cexn => bottom
           | Cbool => bottom
           | Cint => bottom
           | Cchar => bottom
           | Cstring => bottom)

      fun checkKind k =
         (
         ((depthKind [] k) handle IndexError path => raise IndexErrorKind (k, NONE, path));
         ()
         )

      fun checkCon c =
         (
         ((depthCon [] c) handle IndexError path => raise IndexErrorCon (c, NONE, path));
         ()
         )

      fun imposeKindMain path n k =
         (case k of
             Ktype => k
           | Ksing c =>
                Ksing (imposeConMain (0 :: path) n c)
           | Kpi (k1, k2) =>
                Kpi (imposeKindMain (0 :: path) n k1, imposeKindMain (1 :: path) (n+1) k2)
           | Ksigma (k1, k2) =>
                Ksigma (imposeKindMain (0 :: path) n k1, imposeKindMain (1 :: path) (n+1) k2)
           | Kunit => k)

      and imposeConMain path n c =
         (case c of
             Cvar (i, NONE) =>
                if i < n then
                   Cvar (i, SOME n)
                else
                   raise (IndexError (rev path))
           | Cvar (i, SOME j) =>
                if n = j andalso i < j then
                   c
                else
                   raise (IndexError (rev path))
           | Clam (k, c) =>
                Clam (imposeKindMain (0 :: path) n k, imposeConMain (1 :: path) (n+1) c)
           | Capp (c1, c2) =>
                Capp (imposeConMain (0 :: path) n c1, imposeConMain (1 :: path) n c2)
           | Cpair (c1, c2) =>
                Cpair (imposeConMain (0 :: path) n c1, imposeConMain (1 :: path) n c2)
           | Cpi1 c =>
                Cpi1 (imposeConMain (0 :: path) n c)
           | Cpi2 c =>
                Cpi2 (imposeConMain (0 :: path) n c)
           | Cunit => c
           | Carrow (c1, c2) =>
                Carrow (imposeConMain (0 :: path) n c1, imposeConMain (1 :: path) n c2)
           | Cforall (k, c) =>
                Cforall (imposeKindMain (0 :: path) n k, imposeConMain (1 :: path) (n+1) c)
           | Cexists (k, c) =>
                Cexists (imposeKindMain (0 :: path) n k, imposeConMain (1 :: path) (n+1) c)
           | Cprod cl =>
                Cprod (mapi (fn (c, i) => imposeConMain (i :: 0 :: path) n c) cl)
           | Csum cl =>
                Csum (mapi (fn (c, i) => imposeConMain (i :: 0 :: path) n c) cl)
           | Crec c =>
                Crec (imposeConMain (0 :: path) (n+1) c)
           | Ctag c =>
                Ctag (imposeConMain (0 :: path) n c)
           | Cref c =>
                Cref (imposeConMain (0 :: path) n c)
           | Cexn => c
           | Cbool => c
           | Cint => c
           | Cchar => c
           | Cstring => c)

      fun imposeTermMain path n e =
         (case e of
             Tvar _ =>
                e
           | Tlam (v, c, e') =>
                Tlam (v, imposeConMain (1 :: path) n c, imposeTermMain (2 :: path) n e')
           | Tapp (e1, e2) =>
                Tapp (imposeTermMain (0 :: path) n e1, imposeTermMain (1 :: path) n e2)
           | Tplam (k, e') =>
                Tplam (imposeKindMain (0 :: path) n k, imposeTermMain (1 :: path) (n+1) e')
           | Tpapp (e', c) =>
                Tpapp (imposeTermMain (0 :: path) n e', imposeConMain (1 :: path) n c)
           | Tpack (c1, e', c2) =>
                Tpack (imposeConMain (0 :: path) n c1, imposeTermMain (1 :: path) n e', imposeConMain (2 :: path) n c2)
           | Tunpack (v, e1, e2) =>
                Tunpack (v, imposeTermMain (1 :: path) n e1, imposeTermMain (2 :: path) (n+1) e2)
           | Ttuple el =>
                Ttuple (mapi (fn (e, i) => imposeTermMain (i :: 0 :: path) n e) el)
           | Tproj (e', i) =>
                Tproj (imposeTermMain (0 :: path) n e', i)
           | Tinj (e', i, c) =>
                Tinj (imposeTermMain (0 :: path) n e', i, imposeConMain (2 :: path) n c)
           | Tcase (e', arms) =>
                Tcase (imposeTermMain (0 :: path) n e',
                       mapi (fn ((v, e), i) => (v, imposeTermMain (1 :: i :: 1 :: path) n e)) arms)
           | Troll (e', c) =>
                Troll (imposeTermMain (0 :: path) n e', imposeConMain (1 :: path) n c)
           | Tunroll e' =>
                Tunroll (imposeTermMain (0 :: path) n e')
           | Ttag (e1, e2) =>
                Ttag (imposeTermMain (0 :: path) n e1, imposeTermMain (1 :: path) n e2)
           | Tiftag (e1, e2, v, e3, e4) =>
                Tiftag (imposeTermMain (0 :: path) n e1, imposeTermMain (1 :: path) n e2, v, imposeTermMain (3 :: path) n e3, imposeTermMain (4 :: path) n e4)
           | Tnewtag c =>
                Tnewtag (imposeConMain (0 :: path) n c)
           | Traise (e', c) =>
                Traise (imposeTermMain (0 :: path) n e', imposeConMain (1 :: path) n c)
           | Thandle (e1, v, e2) =>
                Thandle (imposeTermMain (0 :: path) n e1, v, imposeTermMain (2 :: path) n e2)
           | Tref e' =>
                Tref (imposeTermMain (0 :: path) n e')
           | Tderef e' =>
                Tderef (imposeTermMain (0 :: path) n e')
           | Tassign (e1, e2) =>
                Tassign (imposeTermMain (0 :: path) n e1, imposeTermMain (1 :: path) n e2)
           | Tbool _ => e
           | Tif (e1, e2, e3) =>
                Tif (imposeTermMain (0 :: path) n e1, imposeTermMain (1 :: path) n e2, imposeTermMain (2 :: path) n e3)
           | Tint _ => e
           | Tchar _ => e
           | Tstring _ => e
           | Tlet (v, e1, e2) =>
                Tlet (v, imposeTermMain (1 :: path) n e1, imposeTermMain (2 :: path) n e2)
           | Tprim (prim, el) =>
                Tprim (prim, mapi (fn (e, i) => imposeTermMain (i :: 1 :: path) n e) el))

      fun imposeKind n k =
         ((imposeKindMain [] n k) handle IndexError path => raise IndexErrorKind (k, SOME n, path))

      fun imposeCon n c =
         ((imposeConMain [] n c) handle IndexError path => raise IndexErrorCon (c, SOME n, path))

      fun imposeTerm n e =
         ((imposeTermMain [] n e) handle IndexError path => raise IndexErrorTerm (e, SOME n, path))

   end