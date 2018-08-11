
structure SubstDirect :> SUBST_DIRECT 
   =
   struct

      open ILDirect
      structure V = Variable
      structure D = VariableDict

      (* substXMain m s n l exp 
       
         if    |s| = n
         then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
      *)

      fun substKindMain m s n l k =
         (case k of
             Ktype => k
           | Ksing c =>
                Ksing (substConMain m s n l c)
           | Kpi (k1, k2) =>
                Kpi (substKindMain m s n l k1, substKindMain (m+1) s n l k2)
           | Ksigma (k1, k2) =>
                Ksigma (substKindMain m s n l k1, substKindMain (m+1) s n l k2)
           | Kunit => k)

      and substConMain m s n l c =
         (case c of
             Cvar (i, NONE) =>
                if i < m then
                   c
                else if i < m+n then
                   substConMain 0 [] 0 m (List.nth (s, i-m))
                else
                   Cvar (i-n+l, NONE)
           | Cvar (i, SOME j) =>
                if i < m then
                   Cvar (i, SOME (j-n+l))
                else if i < m+n then
                   substConMain 0 [] 0 m (List.nth (s, i-m))
                else
                   Cvar (i-n+l, SOME (j-n+l))
           | Clam (k, c) =>
                Clam (substKindMain m s n l k, substConMain (m+1) s n l c)
           | Capp (c1, c2) =>
                Capp (substConMain m s n l c1, substConMain m s n l c2)
           | Cpair (c1, c2) =>
                Cpair (substConMain m s n l c1, substConMain m s n l c2)
           | Cpi1 c =>
                Cpi1 (substConMain m s n l c)
           | Cpi2 c =>
                Cpi2 (substConMain m s n l c)
           | Cunit => c
           | Carrow (c1, c2) =>
                Carrow (substConMain m s n l c1, substConMain m s n l c2)
           | Cforall (k, c) =>
                Cforall (substKindMain m s n l k, substConMain (m+1) s n l c)
           | Cexists (k, c) =>
                Cexists (substKindMain m s n l k, substConMain (m+1) s n l c)
           | Cprod cl =>
                Cprod (map (substConMain m s n l) cl)
           | Csum cl =>
                Csum (map (substConMain m s n l) cl)
           | Crec c =>
                Crec (substConMain (m+1) s n l c)
           | Ctag c =>
                Ctag (substConMain m s n l c)
           | Cref c =>
                Cref (substConMain m s n l c)
           | Cexn => c
           | Cbool => c
           | Cint => c
           | Cchar => c
           | Cstring => c)

      fun substTermMain m s n l e =
         (case e of
             Tvar _ => e
           | Tlam (v, c, e') =>
                Tlam (v, substConMain m s n l c, substTermMain m s n l e')
           | Tapp (e1, e2) =>
                Tapp (substTermMain m s n l e1, substTermMain m s n l e2)
           | Tplam (k, e') =>
                Tplam (substKindMain m s n l k, substTermMain (m+1) s n l e')
           | Tpapp (e', c) =>
                Tpapp (substTermMain m s n l e', substConMain m s n l c)
           | Tpack (c1, e', c2) =>
                Tpack (substConMain m s n l c1, substTermMain m s n l e', substConMain m s n l c2)
           | Tunpack (v, e1, e2) =>
                Tunpack (v, substTermMain m s n l e1, substTermMain (m+1) s n l e2)
           | Ttuple el =>
                Ttuple (map (substTermMain m s n l) el)
           | Tproj (e', i) =>
                Tproj (substTermMain m s n l e', i)
           | Tinj (e', i, c) =>
                Tinj (substTermMain m s n l e', i, substConMain m s n l c)
           | Tcase (e', arms) =>
                Tcase (substTermMain m s n l e', map (fn (vi, ei) => (vi, substTermMain m s n l ei)) arms)
           | Troll (e', c) =>
                Troll (substTermMain m s n l e', substConMain m s n l c)
           | Tunroll e' =>
                Tunroll (substTermMain m s n l e')
           | Ttag (e1, e2) =>
                Ttag (substTermMain m s n l e1, substTermMain m s n l e2)
           | Tiftag (e1, e2, v, e3, e4) =>
                Tiftag (substTermMain m s n l e1, substTermMain m s n l e2, v, substTermMain m s n l e3, substTermMain m s n l e4)
           | Tnewtag c =>
                Tnewtag (substConMain m s n l c)
           | Traise (e', c) =>
                Traise (substTermMain m s n l e', substConMain m s n l c)
           | Thandle (e1, v, e2) =>
                Thandle (substTermMain m s n l e1, v, substTermMain m s n l e2)
           | Tref e' =>
                Tref (substTermMain m s n l e')
           | Tderef e' =>
                Tderef (substTermMain m s n l e')
           | Tassign (e1, e2) =>
                Tassign (substTermMain m s n l e1, substTermMain m s n l e2)
           | Tbool _ => e
           | Tif (e1, e2, e3) =>
                Tif (substTermMain m s n l e1, substTermMain m s n l e2, substTermMain m s n l e3)
           | Tint _ => e
           | Tchar _ => e
           | Tstring _ => e
           | Tlet (v, e1, e2) =>
                Tlet (v, substTermMain m s n l e1, substTermMain m s n l e2)
           | Tprim (prim, el) =>
                Tprim (prim, map (substTermMain m s n l) el))

      fun dsubstTermMain m s n l d e =
         (case e of
             Tvar v =>
                (case VariableDict.find d v of
                    NONE => e
                  | SOME e' =>
                       if m = 0 then
                          e'
                       else
                          substTermMain 0 [] 0 m e')
           | Tlam (v, c, e') =>
                let
                   val v' = V.newvar ()
                in
                   Tlam (v', substConMain m s n l c, 
                         dsubstTermMain m s n l (D.insert d v (Tvar v')) e')
                end
           | Tapp (e1, e2) =>
                Tapp (dsubstTermMain m s n l d e1, dsubstTermMain m s n l d e2)
           | Tplam (k, e') =>
                Tplam (substKindMain m s n l k, dsubstTermMain (m+1) s n l d e')
           | Tpapp (e', c) =>
                Tpapp (dsubstTermMain m s n l d e', substConMain m s n l c)
           | Tpack (c1, e', c2) =>
                Tpack (substConMain m s n l c1, dsubstTermMain m s n l d e', substConMain m s n l c2)
           | Tunpack (v, e1, e2) =>
                let
                   val v' = V.newvar ()
                in
                   Tunpack (v', dsubstTermMain m s n l d e1,
                            dsubstTermMain (m+1) s n l (D.insert d v (Tvar v')) e2)
                end
           | Ttuple el =>
                Ttuple (map (dsubstTermMain m s n l d) el)
           | Tproj (e', i) =>
                Tproj (dsubstTermMain m s n l d e', i)
           | Tinj (e', i, c) =>
                Tinj (dsubstTermMain m s n l d e', i, substConMain m s n l c)
           | Tcase (e', arms) =>
                Tcase (dsubstTermMain m s n l d e',
                       map
                          (fn (vi, ei) =>
                              let
                                 val vi' = V.newvar ()
                              in
                                 (vi', dsubstTermMain m s n l (D.insert d vi (Tvar vi')) ei)
                              end)
                          arms)
           | Troll (e', c) =>
                Troll (dsubstTermMain m s n l d e', substConMain m s n l c)
           | Tunroll e' =>
                Tunroll (dsubstTermMain m s n l d e')
           | Ttag (e1, e2) =>
                Ttag (dsubstTermMain m s n l d e1, dsubstTermMain m s n l d e2)
           | Tiftag (e1, e2, v, e3, e4) =>
                let
                   val v' = V.newvar ()
                in
                   Tiftag (dsubstTermMain m s n l d e1, 
                           dsubstTermMain m s n l d e2, 
                           v', dsubstTermMain m s n l (D.insert d v (Tvar v')) e3, 
                           dsubstTermMain m s n l d e4)
                end
           | Tnewtag c =>
                Tnewtag (substConMain m s n l c)
           | Traise (e', c) =>
                Traise (dsubstTermMain m s n l d e', substConMain m s n l c)
           | Thandle (e1, v, e2) =>
                let
                   val v' = V.newvar ()
                in
                   Thandle (dsubstTermMain m s n l d e1, 
                            v', dsubstTermMain m s n l (D.insert d v (Tvar v')) e2)
                end
           | Tref e' =>
                Tref (dsubstTermMain m s n l d e')
           | Tderef e' =>
                Tderef (dsubstTermMain m s n l d e')
           | Tassign (e1, e2) =>
                Tassign (dsubstTermMain m s n l d e1, dsubstTermMain m s n l d e2)
           | Tbool _ => e
           | Tif (e1, e2, e3) =>
                Tif (dsubstTermMain m s n l d e1, dsubstTermMain m s n l d e2, dsubstTermMain m s n l d e3)
           | Tint _ => e
           | Tchar _ => e
           | Tstring _ => e
           | Tlet (v, e1, e2) =>
                let
                   val v' = V.newvar ()
                in
                   Tlet (v', dsubstTermMain m s n l d e1,
                         dsubstTermMain m s n l (D.insert d v (Tvar v')) e2)
                end
           | Tprim (prim, el) =>
                Tprim (prim, map (dsubstTermMain m s n l d) el))

      fun substKindGen m s l exp =
         let
            val n = length s
         in
            if n = 0 andalso l = 0 then
               exp
            else
               substKindMain m s n l exp
         end

      fun substConGen m s l exp =
         let
            val n = length s
         in
            if n = 0 andalso l = 0 then
               exp
            else
               substConMain m s n l exp
         end

      fun substTermGen m s l exp =
         let
            val n = length s
         in
            if n = 0 andalso l = 0 then
               exp
            else
               substTermMain m s n l exp
         end

      fun dsubstTermGen m s l d exp =
         if D.isEmpty d then
            let
               val n = length s
            in
               if n = 0 andalso l = 0 then
                  exp
               else
                  substTermMain m s n l exp
            end
         else
            dsubstTermMain m s (length s) l d exp

      fun liftKind l exp =
         if l = 0 then
            exp
         else
            substKindMain 0 [] 0 l exp

      fun liftCon l exp =
         if l = 0 then
            exp
         else
            substConMain 0 [] 0 l exp

      fun liftTerm l exp =
         if l = 0 then
            exp
         else
            substTermMain 0 [] 0 l exp

      fun substKind s exp = substKindMain 0 [s] 1 0 exp
      fun substCon s exp = substConMain 0 [s] 1 0 exp
      fun substTerm s exp = substTermMain 0 [s] 1 0 exp

   end
