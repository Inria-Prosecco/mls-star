(* This file gets linked into the library for the purpose of doing an internal
   sanity test without having to link the test files. *)

let dummy32 =
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16 ] @
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16 ]

let bytes_of_list l =
  FStar_Seq_Properties.seq_of_list (List.map (fun x ->
    assert (x <= 255);
    x
  ) l)

let list_of_bytes = FStar_Seq_Properties.seq_to_list

let cs = {
  MLS_Crypto_Builtins.kem_dh = Spec_Agile_DH.DH_Curve25519;
  kem_hash = Spec_Hash_Definitions.SHA2_256;
  aead = Spec_Agile_AEAD.CHACHA20_POLY1305;
  kdf_hash = Spec_Hash_Definitions.SHA2_256;
  signature = MLS_Crypto_Builtins.Ed_25519
}

let debug_buffer s =
  let buf = Buffer.create 1 in
  List.iter (Printf.bprintf buf "%x02d") (list_of_bytes s);
  Buffer.add_string buf "\n";
  Buffer.output_buffer stdout buf

let test () =
  let open MLS_Result in
  let dummy32 = bytes_of_list dummy32 in
  let s = MLS_Crypto_Derived.derive_secret cs dummy32 dummy32 in
  match s with
  | Success s ->
      debug_buffer s;
      flush stdout;
  | _ ->
      print_endline "Test 1 failed with *Error"; ;
  let s = MLS.fresh_key_package dummy32 { signature_key = dummy32; identity = dummy32 } dummy32 in
  match s with
  | Success (s1, s2) ->
      debug_buffer s1;
      debug_buffer s2;
      flush stdout;
  | _ ->
      print_endline "Test 2 failed with *Error"; ;
  print_endline "Done with initial test"
