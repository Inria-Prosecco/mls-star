open Js_of_ocaml

let mls_bytes l =
  FStar_Seq_Properties.seq_of_list (List.map (fun x ->
    assert (x <= 255);
    FStar_UInt8.__uint_to_t (Z.of_int x)
  ) l)

let cs = {
  MLS_Crypto_Builtins.kem_dh = Spec_Agile_DH.DH_Curve25519;
  kem_hash = Spec_Hash_Definitions.SHA2_256;
  aead = Spec_Agile_AEAD.CHACHA20_POLY1305;
  kdf_hash = Spec_Hash_Definitions.SHA2_256;
  signature = MLS_Crypto_Builtins.Ed_25519
}

let _ =
  Js.export_all (object%js
    method debug: _ =
      let s = MLS_Crypto_Derived.derive_secret cs (mls_bytes [ 0; 1 ]) (mls_bytes [ 2; 3 ]) in
      s
  end)

let _ =
  print_endline "...loaded"
