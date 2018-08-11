
signature INSPECT_DIRECT =
   sig

      include INSPECT
      
      val loadKind : ILDirect.kind -> unit
      val loadCon : ILDirect.con -> unit
      val loadTerm : ILDirect.term -> unit

      val extractKind : unit -> ILDirect.kind
      val extractCon : unit -> ILDirect.con
      val extractTerm : unit -> ILDirect.term

      val suppressCon : bool ref

   end
