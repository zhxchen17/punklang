
structure CompactDirect :> COMPACT_DIRECT =
   struct

      open ILDirect
      open HashCons

      val kindTable : kind table = table ()
      val conTable : con table = table ()

      fun destroy () =
         (
         HashCons.destroyTable kindTable;
         HashCons.destroyTable conTable
         )

      fun Cvar' i = Cvar (i, NONE)

      fun consKind k =
         (case k of
             Ktype =>
                cons0 kindTable 0w1 Ktype
           | Ksing c =>
                cons1
                   kindTable 0w2
                   Ksing (consCon c)
           | Kpi (k1, k2) =>
                cons2
                   kindTable 0w3
                   Kpi (consKind k1, consKind k2)
           | Ksigma (k1, k2) =>
                cons2
                   kindTable 0w4
                   Ksigma (consKind k1, consKind k2)
           | Kunit =>
                cons0 kindTable 0w5 Kunit)

      and consCon c =
         (case c of
             Cvar (i, _) =>
                cons1
                   conTable 0w1
                   Cvar' (consInt i)
           | Clam (k, c) =>
                cons2
                   conTable 0w2
                   Clam (consKind k, consCon c)
           | Capp (c1, c2) =>
                cons2
                   conTable 0w3
                   Capp (consCon c1, consCon c2)
           | Cpair (c1, c2) =>
                cons2
                   conTable 0w4
                   Cpair (consCon c1, consCon c2)
           | Cpi1 c =>
                cons1
                   conTable 0w5
                   Cpi1 (consCon c)
           | Cpi2 c =>
                cons1
                   conTable 0w6
                   Cpi2 (consCon c)
           | Cunit =>
                cons0 conTable 0w7 Cunit
           | Carrow (c1, c2) =>
                cons2
                   conTable 0w8
                   Carrow (consCon c1, consCon c2)
           | Cforall (k, c) =>
                cons2
                   conTable 0w9
                   Cforall (consKind k, consCon c)
           | Cexists (k, c) =>
                cons2
                   conTable 0w10
                   Cexists (consKind k, consCon c)
           | Cprod cl =>
                consList
                   conTable 0w11
                   Cprod (map consCon cl)
           | Csum cl =>
                consList
                   conTable 0w12
                   Csum (map consCon cl)
           | Crec c =>
                cons1
                   conTable 0w13
                   Crec (consCon c)
           | Ctag c =>
                cons1
                   conTable 0w14
                   Ctag (consCon c)
           | Cref c =>
                cons1
                   conTable 0w15
                   Cref (consCon c)
           | Cexn =>
                cons0 conTable 0w16 Cexn
           | Cbool =>
                cons0 conTable 0w17 Cbool
           | Cint =>
                cons0 conTable 0w18 Cint
           | Cchar =>
                cons0 conTable 0w19 Cchar
           | Cstring =>
                cons0 conTable 0w20 Cstring)

      fun compactKind k = #1 (consKind k)
      fun compactCon c = #1 (consCon c)

   end
