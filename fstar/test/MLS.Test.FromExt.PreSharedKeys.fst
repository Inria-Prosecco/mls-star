module MLS.Test.FromExt.PreSharedKeys

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.Crypto
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.PSK

val test_psk_one: psk_test -> ML bool
let test_psk_one t =
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    // Unsupported ciphersuite
    false
  end
  | InternalError s -> begin
    failwith ("Internal error! '" ^ s ^ "'\n")
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in
    let psk_data =
      List.map
        (fun (psk:psk_test_psk) -> (
          let psk_id = extract_result (mk_mls_bytes (hex_string_to_bytes psk.psk_id) "test_psk_one" "psk_id") in
          let psk_nonce = extract_result (mk_mls_bytes (hex_string_to_bytes psk.psk_nonce) "test_psk_one" "psk_nonce") in
          (PSKI_external psk_id psk_nonce, hex_string_to_bytes psk.psk)
        ))
        t.psks
    in
    let psk_secret = extract_result (compute_psk_secret psk_data) in
    check_equal "psk_secret" (bytes_to_hex_string) (hex_string_to_bytes t.psk_secret) (psk_secret);
    true
  end

val test_psk: list psk_test -> ML nat
let test_psk =
  test_list "Pre-Shared Keys" test_psk_one
