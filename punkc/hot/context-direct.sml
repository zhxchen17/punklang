
functor ContextDirectFun (val imposeKind : int -> ILDirect.kind -> ILDirect.kind
                          val imposeCon : int -> ILDirect.con -> ILDirect.con)
   :> CONTEXT_DIRECT
   =
   struct
   
      open ILDirect

      type variable = Variable.variable

      structure VariableKey =
         struct
            type t = Variable.variable
            val eq = Variable.eq
            val compare = Variable.compare
         end

      structure Dict = SplayDict (structure Key = VariableKey)

      type context =
         { ksize : int, kctx : kind list, tctx : (int * con) Dict.dict }
         (* ksize = |kctx| *)

      val empty = { ksize=0, kctx=[], tctx=Dict.empty }

      fun lookupKind ({ kctx, ...}:context) i =
         (SubstDirect.liftKind (i+1) (List.nth (kctx, i))
          handle Subscript => raise Misc.TypeError)

      fun lookupType ({ ksize, tctx, ...}:context) v =
         let
            val (n, c) =
               Dict.lookup tctx v
               handle Dict.Absent => raise Misc.TypeError
         in
            SubstDirect.liftCon (ksize-n) c
         end

      fun extendKind { ksize, kctx, tctx } k =
         { ksize = ksize+1,
           kctx = imposeKind ksize k :: kctx,
           tctx = tctx }

      fun extendType { ksize, kctx, tctx } v c =
         { ksize = ksize,
           kctx = kctx,
           tctx = Dict.insert tctx v (ksize, imposeCon ksize c) }

      fun ksize ({ ksize=n, ...}:context) = n

   end


structure ContextDirect =
   ContextDirectFun
   (* Replace these with identity functions for better performance but less error checking. *)
   (val imposeKind = DebugDirect.imposeKind
    val imposeCon = DebugDirect.imposeCon)
