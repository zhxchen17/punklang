
signature EQUIV_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con
      type context = ContextDirect.context

      val whreduce : con -> con
      val whnf : context -> con -> con
      val equiv : context -> con -> con -> kind -> unit
      val samekind : context -> kind -> kind -> unit
      val subkind : context -> kind -> kind -> unit
      val selfify : con -> kind -> kind
      val inhabitant : kind -> con

   end
