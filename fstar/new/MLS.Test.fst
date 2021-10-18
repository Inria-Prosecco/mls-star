module MLS.Test

open FStar.IO
open FStar.All
open MLS.Test.Types
open MLS.Test.Reader
open MLS.Test.FromExt.TreeMath
open MLS.Test.FromExt.Encryption
open MLS.Test.FromExt.KeySchedule
open MLS.Test.FromExt.CommitTranscript
open MLS.Test.FromExt.TreeKEM
open MLS.Test.Utils

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

let run_encryption_tests () =
  match get_testsuite Encryption with
  | Encryption_test l -> begin
    if test_encryption l then (
      IO.print_string ("Encryption: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Encryption: failure\n"
    )
  end
  | _ -> IO.print_string "Encryption: got the wrong type of testsuite (internal error)\n"


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

let run_commit_transcript_tests () =
  IO.print_string "Starting commit / transcript\n";
  match get_testsuite CommitTranscript with
  | CommitTranscript_test l -> begin
    if test_commit_transcript l then (
      IO.print_string ("Commit / Transcript: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Commit / Transcript: failure\n"
    )
  end
  | _ -> IO.print_string "Commit / Transcript: got the wrong type of testsuite (internal error)\n"


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
  run_encryption_tests();
  run_keyschedule_tests ();
  run_treekem_tests ();
  run_commit_transcript_tests ();
  ()
