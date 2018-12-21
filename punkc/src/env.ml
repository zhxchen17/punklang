open Utils

module StringMap = Map.Make(String)
module Int = struct type t = int let compare = compare end
module IntMap = Map.Make(Int)

type context =
  { ksize: int; kctx: Ast.kind list; tctx: (int * Ast.ty) IntMap.t }

type env = { var_id_map: int StringMap.t;
             ctx: context;
             is_top: bool;
             mut_set: (int, unit) Hashtbl.t;
             elab_con_map: (int, Tir.con) Hashtbl.t;
             persistent_set: (int, unit) Hashtbl.t }

let empty_ctx () = { ksize = 0; kctx = []; tctx = IntMap.empty }

let empty_env () = { var_id_map = StringMap.empty;
                     ctx = empty_ctx ();
                     is_top = true;
                     mut_set = Hashtbl.create table_size;
                     elab_con_map = Hashtbl.create table_size;
                     persistent_set = Hashtbl.create table_size }

let add_id env id name =
  { env with var_id_map = StringMap.add name id env.var_id_map; }

let find_id_opt env name = StringMap.find_opt name env.var_id_map

let lookup_kind ({ kctx }: context) i =
  Subst.lift_kind (i + 1) (List.nth kctx i)

let lookup_type ({ ksize; tctx }: context) v =
  match IntMap.find_opt v tctx with
  | Some (n, c) -> Subst.lift_con (ksize - n) c
  | None -> raise (TypeError ("lookup_type: " ^ (string_of_int v)))

let extend_kind { ksize; kctx; tctx } k =
  { ksize = ksize + 1; kctx = k::kctx; tctx = tctx }

let extend_type { ksize; kctx; tctx } v c =
  { ksize = ksize; kctx = kctx; tctx = IntMap.add v (ksize, c) tctx}

let ksize ({ ksize }: context) = ksize

let new_func_name () =
  let (id, _) = Var.newvar None in
  "f" ^ string_of_int id

let mangle_name id = "v" ^ string_of_int id
