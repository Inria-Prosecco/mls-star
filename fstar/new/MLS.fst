module MLS

open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let cs = Success?.v (MLS.Crypto.Derived.ciphersuite_from_nt MLS.NetworkTypes.CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519)

let group_id = MLS.TreeSync.Types.group_id_t
let state g = s:MLS.TreeSync.Types.state_t { g == s.group_id }

let fresh_key_package e { identity; signature_key } =
  let open MLS.TreeSync.Types in
  let open MLS.Crypto in
  let open MLS.NetworkTypes in
  let open MLS.NetworkBinder in
  let open MLS.Parser in
  let open MLS.Result in // Already opened, but we don't want Parser.bind in the scope
  assume (hpke_private_key_length cs < 32);
  key_pair <-- hpke_gen_keypair cs e;
  let ((private_key: bytes), public_key) = key_pair in
  let unsigned_leaf_package: leaf_package_t = {
    credential = {
      version = 0;
      identity;
      signature_key;
    };
    version = 0;
    content = ps_leaf_package_content.serialize ({public_key});
    extensions = (* TODO *) Seq.empty;
    signature = Seq.empty;
  } in
  signature <-- (
    unsigned_key_package <-- treesync_to_keypackage cs unsigned_leaf_package;
    let tbs = ps_key_package_tbs.serialize (key_package_get_tbs unsigned_key_package) in
    assume (sign_nonce_length cs < 32);
    sign_sign cs ( (* private signature key *) admit ()) tbs (mk_randomness (Seq.slice e 0 (sign_nonce_length cs)))
  );
  let leaf_package = { unsigned_leaf_package with signature } in
  key_package <-- treesync_to_keypackage cs leaf_package;
  return (ps_key_package.serialize key_package, private_key)

#push-options "--fuel 2"
let create e { identity; signature_key } g =
  let c: MLS.TreeSync.Types.credential_t = {
    identity;
    signature_key;
    version = 0
  } in
  let t = MLS.TreeSync.create_tree 1 1 c (Seq.seq_of_list [ Some c ]) in
  MLS.TreeSync.Types.mk_initial_state g 1 1 t
#pop-options


let add #g state key_package = admit()
let remove #g state p = admit()
let update #g state e = admit()
let send #g state e data = admit()
let process_welcome_message w lookup = admit()
let process_group_message #g state msg = admit()
