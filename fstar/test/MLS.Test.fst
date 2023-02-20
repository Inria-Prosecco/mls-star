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

val run_tests: #a:Type -> string -> test_type -> ts_pre:(testsuite -> bool) -> (ts:testsuite{ts_pre ts} -> list a) -> (list a -> ML nat) -> ML unit
let run_tests #a name ty ts_pre extract_testsuite run_test =
  let testsuite = get_testsuite ty in
  if not (ts_pre testsuite) then
    failwith (name ^ ": failed to read tests")
  else (
    let testsuite = extract_testsuite testsuite in
    IO.print_string (name ^ ": running tests...\n");
    let n_run = run_test testsuite in
    IO.print_string (name ^ ": success! (" ^ nat_to_string n_run ^ "/" ^ nat_to_string (List.Tot.length testsuite) ^ ")\n")
  )

let run_treemath_tests () =
  run_tests "Tree Math" TreeMath TreeMath_test? TreeMath_test?._0 test_treemath

let run_crypto_basics_tests () =
  run_tests "Crypto Basics" CryptoBasics CryptoBasics_test? CryptoBasics_test?._0 test_crypto_basics

let run_secret_tree_tests () =
  run_tests "Secret Tree" SecretTree SecretTree_test? SecretTree_test?._0 test_secret_tree

let run_message_protection_tests () =
  run_tests "Message Protection" MessageProtection MessageProtection_test? MessageProtection_test?._0 test_message_protection

let run_keyschedule_tests () =
  run_tests "Key Schedule" KeySchedule KeySchedule_test? KeySchedule_test?._0 test_keyschedule

let run_psk_tests () =
  run_tests "Pre-Shared Keys" PreSharedKeys PreSharedKeys_test? PreSharedKeys_test?._0 test_psk

let main =
  MLS.Test.Internal.test ();
  run_treemath_tests ();
  run_crypto_basics_tests ();
  run_secret_tree_tests ();
  run_message_protection_tests ();
  run_keyschedule_tests ();
  run_psk_tests ();
  run_self_treekem_test ();
  ()
