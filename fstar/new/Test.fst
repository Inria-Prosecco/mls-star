module Test

open FStar.IO
open FStar.All
open Test.Types
open Test.Reader
open Test.TreeMath
open Test.Utils

let main =
  match get_testsuite TreeMath with
  | TreeMath_test l -> begin
    if test_treemath l then (
      IO.print_string ("TreeMath: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "TreeMath: failure\n"
    )
  end
  | _ -> IO.print_string "TreeMath: got the wrong type of testsuite (internal error)\n"
