open Ast

let run_tests () =
  assert (Eint 42 = Main.parse_expr "42");
  assert (Eop (Add, [Eint 21; Eint 21]) = Main.parse_expr "21 + 21");
  assert (Evar (-1, Some "x") = Main.parse_expr "x");
  let (n, _) = Var.newvar None in
  assert ((n + 1, None) = Var.newvar None);
  assert ((n + 2, Some "x") = Var.newvar (Some "x"));
  let pkg = new Main.package in
  let ph0 =
    pkg#parse "let y: int = 41; func foo(x: int): int { return x + y; }" in
  assert (
    [Sdecl ((n + 3, Some "y"), Some Cint, Eint 41);
     Sdecl ((n + 5, Some "foo"), None,
            Efunc([(n + 4, Some "x"), Cint], Cint,
                  (Sblk [Sret (Eop (Add, [(Evar (-1, Some "x"));
                                          (Evar (-1, Some "y"))]))])))]
          = ph0);
  pkg#print_defs ();
  let ph1 = pkg#resolve ph0 in
  assert (
    [Sdecl ((n + 3, Some "y"), Some Cint, Eint 41);
     Sdecl ((n + 5, Some "foo"), None,
            Efunc([(n + 4, Some "x"), Cint], Cint,
                  (Sblk [Sret (Eop (Add, [(Evar (n + 4, Some "x"));
                                          (Evar (n + 3, Some "y"))]))])))]
          = ph1);
;;

run_tests ()
