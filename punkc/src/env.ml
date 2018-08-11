open Ast

module StringMap = Map.Make(String)
module Int = struct type t = int let compare = compare end
module IntMap = Map.Make(Int)

type context = { ksize: int; kctx: kind list; tctx: con IntMap.t }

type env = { var_id_map: int StringMap.t;
             ctx: context }

let new_env () = { var_id_map = StringMap.empty;
                   ctx = { ksize = 0; kctx = []; tctx = IntMap.empty } }

let add_id env id name =
  { env with var_id_map = StringMap.add name id env.var_id_map; }

let find_id_opt env name = StringMap.find_opt name env.var_id_map

let lookup_kind ({ kctx }: context) i =
  Subst.lift_kind (i + 1) (List.nth kctx i)
