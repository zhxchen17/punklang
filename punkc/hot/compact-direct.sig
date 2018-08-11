
signature COMPACT_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con

      val compactKind : kind -> kind
      val compactCon : con -> con

      val destroy : unit -> unit

   end
