
structure InspectDirect :> INSPECT_DIRECT =
   struct

      open InspectionValue
      open ILDirect

      exception TagKind of kind
      exception TagCon of con
      exception TagTerm of term
      exception TagPrim of Prim.prim

      val TK = Abs o TagKind
      val TC = Abs o TagCon
      val TT = Abs o TagTerm

      fun Data0 str = Data (str, [])

      val nope = ref false  (* don't modify this *)
      val suppressCon = ref false

      fun kindTool ex =
         (case ex of
             TagKind k =>
                SOME
                ((case k of
                     Ktype =>
                        Data0 "Ktype"
                   | Ksing c =>
                        Data ("Ksing", [TC c])
                   | Kpi (k1, k2) =>
                        Data ("Kpi", [TK k1, TK k2])
                   | Ksigma (k1, k2) =>
                        Data ("Ksigma", [TK k1, TK k2])
                   | Kunit =>
                        Data0 "Kunit"),
                 "kind", nope)
           | _ =>
                NONE)

      fun conTool ex =
         (case ex of
             TagCon c =>
                SOME
                ((case c of
                     Cvar (i, jo) =>
                        Data ("Cvar", [Int i, Option (Option.map Int jo)])
                   | Clam (k, c) =>
                        Data ("Clam", [TK k, TC c])
                   | Capp (c1, c2) =>
                        Data ("Capp", [TC c1, TC c2])
                   | Cpair (c1, c2) =>
                        Data ("Cpair", [TC c1, TC c2])
                   | Cpi1 c =>
                        Data ("Cpi1", [TC c])
                   | Cpi2 c =>
                        Data ("Cpi2", [TC c])
                   | Cunit =>
                        Data0 "Cunit"
                   | Cforall (k, c) =>
                        Data ("Cforall", [TK k, TC c])
                   | Cexists (k, c) =>
                        Data ("Cexists", [TK k, TC c])
                   | Carrow (c1, c2) =>
                        Data ("Carrow", [TC c1, TC c2])
                   | Cprod cl =>
                        Data ("Cprod", [List (map TC cl)])
                   | Csum cl =>
                        Data ("Csum", [List (map TC cl)])
                   | Crec c =>
                        Data ("Crec", [TC c])
                   | Ctag c =>
                        Data ("Ctag", [TC c])
                   | Cref c =>
                        Data ("Cref", [TC c])
                   | Cexn =>
                        Data0 "Cexn"
                   | Cbool =>
                        Data0 "Cbool"
                   | Cint =>
                        Data0 "Cint"
                   | Cchar =>
                        Data0 "Cchar"
                   | Cstring =>
                        Data0 "Cstring"),
                 "con", suppressCon)
           | _ =>
                NONE)

      fun termTool ex =
         (case ex of
             TagTerm e =>
                SOME
                ((case e of
                     Tvar v =>
                        Data ("Tvar", [Int v])
                   | Tlam (v, c, e) =>
                        Data ("Tlam", [Int v, TC c, TT e])
                   | Tapp (e1, e2) =>
                        Data ("Tapp", [TT e1, TT e2])
                   | Tplam (k, e) =>
                        Data ("Tplam", [TK k, TT e])
                   | Tpapp (e, c) =>
                        Data ("Tpapp", [TT e, TC c])
                   | Tpack (c1, e, c2) =>
                        Data ("Tpack", [TC c1, TT e, TC c2])
                   | Tunpack (v, e1, e2) =>
                        Data ("Tunpack", [Int v, TT e1, TT e2])
                   | Ttuple el =>
                        Data ("Ttuple", [List (map TT el)])
                   | Tproj (e, i) =>
                        Data ("Tproj", [TT e, Int i])
                   | Tinj (e, i, c) =>
                        Data ("Tinj", [TT e, Int i, TC c])
                   | Tcase (e, match) =>
                        Data ("Tcase", [TT e,
                                        List (map
                                                 (fn (vi, ei) =>
                                                     Tuple [Int vi, TT ei])
                                                 match)])
                   | Troll (e, c) =>
                        Data ("Troll", [TT e, TC c])
                   | Tunroll e =>
                        Data ("Tunroll", [TT e])
                   | Ttag (e1, e2) =>
                        Data ("Ttag", [TT e1, TT e2])
                   | Tiftag (e1, e2, v, e3, e4) =>
                        Data ("Tiftag", [TT e1, TT e2, Int v, TT e3, TT e4])
                   | Tnewtag c =>
                        Data ("Tnewtag", [TC c])
                   | Traise (e, c) =>
                        Data ("Traise", [TT e, TC c])
                   | Thandle (e1, v, e2) =>
                        Data ("Thandle", [TT e1, Int v, TT e2])
                   | Tref e =>
                        Data ("Tref", [TT e])
                   | Tderef e =>
                        Data ("Tderef", [TT e])
                   | Tassign (e1, e2) =>
                        Data ("Tassign", [TT e1, TT e2])
                   | Tbool b =>
                        Data ("Tbool", [Bool b])
                   | Tif (e1, e2, e3) =>
                        Data ("Tif", [TT e1, TT e2, TT e3])
                   | Tint i =>
                        Data ("Tint", [Int i])
                   | Tchar ch =>
                        Data ("Tchar", [Char ch])
                   | Tstring str =>
                        Data ("Tstring", [String str])
                   | Tlet (v, e1, e2) =>
                        Data ("Tlet", [Int v, TT e1, TT e2])
                   | Tprim (prim, el) =>
                        Data ("Tprim", [Abs (TagPrim prim), List (map TT el)])),
                 "term", nope)
           | _ =>
                NONE)

      val tools = [kindTool, conTool, termTool]

      structure Inspect = InspectFun (val tools = tools)
      open Inspect

      val loadKind = Inspect.load o TagKind
      val loadCon = Inspect.load o TagCon
      val loadTerm = Inspect.load o TagTerm

      fun extractKind () =
         (case Inspect.extract () of
             TagKind x => x
           | _ => raise Inspect.Extract)

      fun extractCon () =
         (case Inspect.extract () of
             TagCon x => x
           | _ => raise Inspect.Extract)

      fun extractTerm () =
         (case Inspect.extract () of
             TagTerm x => x
           | _ => raise Inspect.Extract)

   end

