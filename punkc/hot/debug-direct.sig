
signature DEBUG_DIRECT =
   sig

      type kind = ILDirect.kind
      type con = ILDirect.con
      type term = ILDirect.term

      exception IndexErrorKind of kind * int option * int list
      exception IndexErrorCon of con * int option * int list
      exception IndexErrorTerm of term * int option * int list

      val checkKind : kind -> unit
      val checkCon : con -> unit

      val imposeKind : int -> kind -> kind
      val imposeCon : int -> con -> con
      val imposeTerm : int -> term -> term

   end
