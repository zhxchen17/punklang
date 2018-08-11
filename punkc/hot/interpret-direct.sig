
signature INTERPRET_DIRECT =
   sig

      type term = ILDirect.term
      type result = ResultDirect.result

      type env = result VariableDict.dict

      val eval : env -> term -> result

   end

      