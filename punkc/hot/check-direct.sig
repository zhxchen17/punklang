
signature CHECK_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con
      type term = ILDirect.term
      type context = ContextDirect.context

      val checkKind : context -> kind -> unit
      val inferCon : context -> con -> kind
      val checkCon : context -> con -> kind -> unit
      val inferTerm : context -> term -> con
      val checkTerm : context -> term -> con -> unit

      val checkProgram : con -> term -> unit

   end
