module Test

open FStar.IO
open FStar.All
open Test.Types
open Test.Reader
open Test.TreeMath
open Test.KeySchedule
open Test.TreeKEM
open Test.Utils

let run_treemath_tests () =
  match get_testsuite TreeMath with
  | TreeMath_test l -> begin
    if test_treemath l then (
      IO.print_string ("TreeMath: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "TreeMath: failure\n"
    )
  end
  | _ -> IO.print_string "TreeMath: got the wrong type of testsuite (internal error)\n"

let run_keyschedule_tests () =
  match get_testsuite KeySchedule with
  | KeySchedule_test l -> begin
    if test_keyschedule l then (
      IO.print_string ("KeySchedule: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "KeySchedule: failure\n"
    )
  end
  | _ -> IO.print_string "KeySchedule: got the wrong type of testsuite (internal error)\n"

let run_treekem_tests () =
  IO.print_string "Starting treekem\n";
  match get_testsuite TreeKEM with
  | TreeKEM_test l -> begin
    if test_treekem l then (
      IO.print_string ("TreeKEM: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "TreeKEM: failure\n"
    )
  end
  | _ -> IO.print_string "TreeKEM: got the wrong type of testsuite (internal error)\n"

let main =
  run_treemath_tests ();
  //run_keyschedule_tests ();
  run_treekem_tests ()
