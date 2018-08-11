
structure ResultDirect =
   struct

      datatype result =
         Rfn of result -> result
       | Rpfn of unit -> result
       | Rpack of result
       | Rtuple of result list
       | Rinj of result * int
       | Rroll of result
       | Rtag of unit ref
       | Rexn of unit ref * result
       | Rref of result ref
       | Rbool of bool
       | Rint of int
       | Rchar of char
       | Rstring of string

      exception Wrong
      exception RaiseExn of result

   end
