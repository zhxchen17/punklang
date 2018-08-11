
signature CONTEXT_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con
      type variable = Variable.variable

      type context

      val empty : context

      val lookupKind : context -> int -> kind
      val lookupType : context -> variable -> con

      val extendKind : context -> kind -> context
      val extendType : context -> variable -> con -> context

      val ksize : context -> int

   end
