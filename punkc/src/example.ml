open Ast

let run_tests () =
  assert (Eint 42 = Main.parse_expr "42");
  assert (Eop (Add, [Eint 21; Eint 21]) = Main.parse_expr "21 + 21");
  assert (Evar (-1, Some "x") = Main.parse_expr "x");
  let (n, _) = Var.newvar None in
  assert ((n + 1, None) = Var.newvar None);
  assert ((n + 2, Some "x") = Var.newvar (Some "x"));
  let prog = "let y: int = 41; func foo(x: int): int { return x + y; }" in
  let pkg = new Main.package in
  let ph0 = pkg#parse prog in
  assert (
    [Sdecl ((n + 3, Some "y"), Immutable, Some Cint, Eint 41);
     Sdecl ((n + 5, Some "foo"), Immutable, None,
            Efunc([(n + 4, Some "x"), Immutable, Cint], Cint,
                  (Sblk [Sret (Eop (Add, [(Evar (-1, Some "x"));
                                          (Evar (-1, Some "y"))]))])))]
    = ph0);
  assert (fst (Check.infer_expr (Env.empty_ctx ()) (Eop (Add, [Eint 1; Eint 1]))) = Cint);
  let ph1 = pkg#resolve ph0 in
  assert (
    [Sdecl ((n + 3, Some "y"), Immutable, Some Cint, Eint 41);
     Sdecl ((n + 5, Some "foo"), Immutable, None,
            Efunc([(n + 4, Some "x"), Immutable, Cint], Cint,
                  (Sblk [Sret (Eop (Add, [(Evar (n + 4, Some "x"));
                                          (Evar (n + 3, Some "y"))]))])))]
    = ph1);
  let empty = Env.empty_ctx () in
  assert (Equiv.same_kind empty Kunit Kunit = ());
  assert (fst (Check.infer_stmt empty (Sblk [Sdecl ((0, Some "y"), Immutable, Some Cint, Eint 1); Sret (Evar(0, Some "y"))])) = Cint);
  let ph2 = pkg#type_check ph1 in
  assert (
    [Sdecl ((n + 3, Some "y"), Immutable, Some Cint, Eint 41);
     Sdecl ((n + 5, Some "foo"), Immutable, Some (Carrow ([Cint], Cint)),
            Efunc([(n + 4, Some "x"), Immutable, Cint], Cint,
                  (Sblk [Sret (Eop (Add, [(Evar (n + 4, Some "x"));
                                          (Evar (n + 3, Some "y"))]))])))]
    = ph2);
  let compiler = new Main.package in
  let _ = compiler#compile prog in
  let c' = new Main.package in
  let m' = c'#compile "let y: int = 41;

struct pair_t {
  x: int,
  y: int
}

func foo(x: int): int {
  let z: pair_t = pair_t { y: 1, x: 1 };
  printf [\"%d\", z.x];
  return x + y;
}
"
  in
  Llvm.dump_module m';
;;

run_tests ()
