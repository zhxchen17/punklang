
structure ILDirect =
   struct

      datatype kind =
         Ktype
       | Ksing of con
       | Kpi of kind * kind     (* binds *)
       | Ksigma of kind * kind  (* binds *)
       | Kunit

      and con =
         Cvar of int * int option
       | Clam of kind * con     (* binds *)
       | Capp of con * con
       | Cpair of con * con
       | Cpi1 of con
       | Cpi2 of con
       | Cunit

       | Carrow of con * con
       | Cforall of kind * con  (* binds *)
       | Cexists of kind * con  (* binds *)
       | Cprod of con list
       | Csum of con list
       | Crec of con            (* binds *)
       | Ctag of con
       | Cref of con
       | Cexn
       | Cbool
       | Cint
       | Cchar
       | Cstring

      type variable = Variable.variable

      datatype term =
         Tvar of variable

       | Tlam of variable * con * term
       | Tapp of term * term

       | Tplam of kind * term                (* binds *)
       | Tpapp of term * con

       | Tpack of con * term * con
       | Tunpack of variable * term * term   (* binds *)

       | Ttuple of term list
       | Tproj of term * int

       | Tinj of term * int * con
       | Tcase of term * (variable * term) list

       | Troll of term * con
       | Tunroll of term

       | Ttag of term * term
       | Tiftag of term * term * variable * term * term
       | Tnewtag of con

       | Traise of term * con
       | Thandle of term * variable * term

       | Tref of term
       | Tderef of term
       | Tassign of term * term

       | Tbool of bool
       | Tif of term * term * term

       | Tint of int
       | Tchar of char
       | Tstring of string

       | Tlet of variable * term * term
       | Tprim of Prim.prim * term list

   end
