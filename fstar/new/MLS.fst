module MLS

open MLS.Result

// TODO: why?
friend MLS.Crypto.Builtins

let cs = {
  MLS.Crypto.Builtins.kem_dh = Spec.Agile.DH.DH_Curve25519;
  kem_hash = Spec.Hash.Definitions.SHA2_256;
  aead = Spec.Agile.AEAD.CHACHA20_POLY1305;
  kdf_hash = Spec.Hash.Definitions.SHA2_256;
  signature = MLS.Crypto.Builtins.Ed_25519
}

let group_id = MLS.TreeSync.Types.group_id_t
let state g = s:MLS.TreeSync.Types.state_t { g == s.group_id }

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let fresh_key_package e { identity; signature_key } =
  let open MLS.NetworkTypes in
  let version = PV_mls10 in
  let cipher_suite = CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519 in
  let basic_credential = {
    identity;
    signature_scheme = SA_ed25519;
    signature_key
  } in
  let credential = C_basic basic_credential in
  admit (); // TODO: don't know how to generate something sensible for extensions
  let extensions = Seq.empty in
  let signature = (* TODO *) Seq.empty in
  MLS.Result.bind (MLS.Crypto.Builtins.hpke_gen_keypair cs e) (fun key_pair ->
  let (private_key: bytes), public_key = key_pair in
  let key_package: key_package_nt =
    { public_key; cipher_suite; version; credential; extensions; signature }
  in
  let key_package: bytes = ps_key_package.MLS.Parser.serialize key_package in
  MLS.Result.return (key_package, private_key))

#reset-options
let create e { identity; signature_key } g =
  let c: MLS.TreeSync.Types.credential_t = {
    identity;
    signature_key;
    version = 0
  } in
  let t = MLS.TreeSync.create_tree 1 1 c (Seq.seq_of_list [ Some c ]) in
  MLS.TreeSync.Types.mk_initial_state g 1 1 t
