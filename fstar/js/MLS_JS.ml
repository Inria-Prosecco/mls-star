open Js_of_ocaml

let mls_bytes l =
  FStar_Seq_Properties.seq_of_list (List.map (fun x ->
    assert (x <= 255);
    x
  ) l)

let cs = {
  MLS_Crypto_Builtins.kem_dh = Spec_Agile_DH.DH_Curve25519;
  kem_hash = Spec_Hash_Definitions.SHA2_256;
  aead = Spec_Agile_AEAD.CHACHA20_POLY1305;
  kdf_hash = Spec_Hash_Definitions.SHA2_256;
  signature = MLS_Crypto_Builtins.Ed_25519
}

let dummy =
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16 ] @
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16 ]

let _ =
  Js.export_all (object%js
    method debug: _ =
      let s = MLS_Crypto_Derived.derive_secret cs
        (mls_bytes dummy)
        (mls_bytes dummy)
      in
      match s with
      | Success s ->
          let buf = Buffer.create 1 in
          List.iter (Printf.bprintf buf "%x02d") (FStar_Seq_Properties.seq_to_list s);
          Buffer.add_string buf "\n";
          Buffer.output_buffer stdout buf
      | _ ->
          print_endline "Test failed with *Error"
  end)

let _ =
  print_endline "...loaded"
