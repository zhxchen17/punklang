open OUnit

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (Bytes.to_string s)

let root_dir = "../tests"
let prefix = "punkc_"

let () = Random.self_init ()
let test_id = Printf.sprintf "%x" (Random.bits ())

let temp_dir = (Filename.get_temp_dir_name ()) ^ "/punkc/test_" ^ test_id
let punkc_dir = (Filename.dirname temp_dir)
let temp_file = Filename.temp_file ~temp_dir

let tests =
  Sys.readdir root_dir
  |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".pk")

let _ = Sys.command ("mkdir -p " ^ punkc_dir)

let rm_list =
  Sys.readdir punkc_dir
  |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".rmv")
  |> List.map (Filename.concat punkc_dir)

let _ =
  Sys.command
    ("rm -rf " ^
     (String.concat " " (List.map Filename.remove_extension rm_list)))
let _ = Sys.command ("rm -f " ^ (String.concat " " rm_list))
let _ = Sys.command ("touch " ^ temp_dir ^ ".rmv")
let _ = Sys.command ("mkdir -p " ^ temp_dir)

let test_gen file =
  let pkg = (Filename.chop_extension file) in
  pkg >:: fun _ ->
    let pk_file = Filename.concat root_dir file in
    let expect_file = Filename.concat root_dir (pkg ^ ".expect") in
    let compiler = new Main.package in
    let llvm_module = compiler#compile (load_file pk_file) in
    let name = prefix ^ pkg in
    let ll_file = temp_file name ".ll" in
    let obj_file = temp_file name ".o" in
    let exe_file = temp_file name ".exe" in
    let out_file = temp_file name ".out" in
    let diff_file = temp_file name ".diff" in
    let () = Llvm.print_module ll_file llvm_module in
    let _ = Sys.command ("llc -relocation-model=pic -filetype=obj -o=" ^
                         obj_file ^ " " ^ ll_file) in
    let _ = Sys.command ("gcc " ^ obj_file ^ " -o " ^ exe_file) in
    let _ = Sys.command (exe_file ^ " > " ^ out_file) in
    let ret =
      Sys.command
        ("diff " ^ expect_file ^ " " ^ out_file ^ " > " ^ diff_file) in
    assert_equal ret 0

let unit_tests = "unit tests" >::: (List.map test_gen tests)

let _ = run_test_tt_main unit_tests
