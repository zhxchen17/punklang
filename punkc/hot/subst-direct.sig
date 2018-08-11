
signature SUBST_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con
      type term = ILDirect.term
      
      (* For X in {Kind, Con, Term}:
         substXGen m [s0, .. sn-1] l exp = exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]

         If    d = v0 |-> e0 .. vp-1 |-> ep-1
         then  dsubstTermGen m [s0, .. sn-1] l d e
               = [e0[^m] .. ep-1[^m] / v0 .. vp-1] (e[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m])
      *)

      val substKindGen : int -> con list -> int -> kind -> kind
      val substConGen : int -> con list -> int -> con -> con
      val substTermGen : int -> con list -> int -> term -> term
      val dsubstTermGen : int -> con list -> int -> term VariableDict.dict -> term -> term

      val liftKind : int -> kind -> kind
      val liftCon : int -> con -> con
      val liftTerm : int -> term -> term

      val substKind : con -> kind -> kind
      val substCon : con -> con -> con
      val substTerm : con -> term -> term

   end
