module MLS.Test.FromExt.PreSharedKeys

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.Crypto
open MLS.TreeDEM.PSK

val test_psk_one: psk_test -> ML bool
let test_psk_one t =
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
    true
  end
  | InternalError s -> begin
    IO.print_string ("Internal error! '" ^ s ^ "'\n");
    false
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in
    let psk_data =
      List.map
        (fun psk -> ({
          id = PSKI_external (hex_string_to_bytes psk.psk_id);
          nonce = (hex_string_to_bytes psk.psk_nonce);
        }, hex_string_to_bytes psk.psk))
        t.psks
    in
    let psk_secret = extract_result (compute_psk_secret psk_data) in
    check_equal "psk_secret" (bytes_to_hex_string) (hex_string_to_bytes t.psk_secret) (psk_secret)
  end

val test_psk: list psk_test -> ML bool
let test_psk =
  test_list "Pre-Shared Keys" test_psk_one
