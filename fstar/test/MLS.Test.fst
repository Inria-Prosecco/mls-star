module MLS.Test

open FStar.IO
open FStar.All
open MLS.Test.Types
open MLS.Test.Reader
open MLS.Test.FromExt.TreeMath
open MLS.Test.FromExt.CryptoBasics
open MLS.Test.FromExt.SecretTree
open MLS.Test.FromExt.MessageProtection
open MLS.Test.FromExt.KeySchedule
open MLS.Test.FromExt.PreSharedKeys
open MLS.Test.FromExt.CommitTranscript
open MLS.Test.FromExt.TreeKEM
open MLS.Test.Self.TreeKEM
open MLS.Test.Utils
open MLS.StringUtils

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

let run_crypto_basics_tests () =
  match get_testsuite CryptoBasics with
  | CryptoBasics_test l -> begin
    if test_crypto_basics l then (
      IO.print_string ("Crypto Basics: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Crypto Basics: failure\n"
    )
  end
  | _ -> IO.print_string "Crypto Basics: got the wrong type of testsuite (internal error)\n"

let run_secret_tree_tests () =
  match get_testsuite SecretTree with
  | SecretTree_test l -> begin
    if test_secret_tree l then (
      IO.print_string ("Secret Tree: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Secret Tree: failure\n"
    )
  end
  | _ -> IO.print_string "Secret Tree: got the wrong type of testsuite (internal error)\n"

let run_message_protection_tests () =
  match get_testsuite MessageProtection with
  | MessageProtection_test l -> begin
    if test_message_protection l then (
      IO.print_string ("Message Protection: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Message Protection: failure\n"
    )
  end
  | _ -> IO.print_string "Message Protection: got the wrong type of testsuite (internal error)\n"

let run_keyschedule_tests () =
  match get_testsuite KeySchedule with
  | KeySchedule_test l -> begin
    if test_keyschedule l then (
      IO.print_string ("Key Schedule: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Key Schedule: failure\n"
    )
  end
  | _ -> IO.print_string "Key Schedule: got the wrong type of testsuite (internal error)\n"

let run_psk_tests () =
  match get_testsuite PreSharedKeys with
  | PreSharedKeys_test l -> begin
    if test_psk l then (
      IO.print_string ("Pre-Shared Keys: success (" ^ (nat_to_string (List.Tot.length l)) ^ " tests)\n")
    ) else (
      IO.print_string "Pre-Shared Keys: failure\n"
    )
  end
  | _ -> IO.print_string "Pre-Shared Keys: got the wrong type of testsuite (internal error)\n"

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
  MLS.Test.Internal.test ();
  run_treemath_tests ();
  run_crypto_basics_tests ();
  run_secret_tree_tests ();
  run_message_protection_tests ();
  run_keyschedule_tests ();
  run_psk_tests ();
  //run_treekem_tests ();
  //run_commit_transcript_tests ();
  run_self_treekem_test ();
  ()
