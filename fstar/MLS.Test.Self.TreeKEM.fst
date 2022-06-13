module MLS.Test.Self.TreeKEM

open FStar.All
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.Extensions
open MLS.TreeSync.ExternalPath
open MLS.TreeSync
open MLS.TreeSync.Hash
open MLS.TreeKEM
open MLS.TreeSyncTreeKEMBinder
open MLS.Test.Utils
open MLS.StringUtils
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type participant_secrets (bytes:Type0) {|crypto_bytes bytes|} = {
  sign_sk: sign_private_key bytes;
  leaf_secret: lbytes bytes (hpke_private_key_length #bytes);
}

type mls_state (bytes:Type0) {|crypto_bytes bytes|} = {
  public: state_t bytes;
  secrets: list (nat & participant_secrets bytes);
}

type test_state = {
  n_add: nat;
  n_update: nat;
  n_remove: nat;
}

type state (bytes:Type0) {|crypto_bytes bytes|} = {
  rng: rand_state;
  mls: mls_state bytes;
  test: test_state;
}

type op_type = | Add | Update | Remove

val get_secret: #a:Type -> list (nat & a) -> nat -> ML a
let rec get_secret #a l x =
  extract_result (from_option "" (List.Tot.assoc x l))

#push-options "--fuel 1 --ifuel 1"
val update_secret: #a:Type -> list (nat & a) -> (nat & a) -> ML (list (nat & a))
let rec update_secret #a l (x, s) =
  match l with
  | [] -> failwith "remove_secret: couldn't find index"
  | (hx, hs)::t ->
    if hx = x then
      (x,s)::t
    else
      (hx,hs)::(update_secret t (x,s))
#pop-options

#push-options "--fuel 1 --ifuel 1"
val remove_secret: #a:Type -> list (nat & a) -> nat -> ML (list (nat & a))
let rec remove_secret #a l x =
  match l with
  | [] -> failwith "remove_secret: couldn't find index"
  | (hx, hs)::t ->
    if hx = x then
      t
    else
      (hx,hs)::(remove_secret t x)
#pop-options

#push-options "--ifuel 1"
//TODO: copy-pasted from MLS.fst
val gen_leaf_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> participant_secrets bytes -> sign_public_key bytes -> hpke_public_key bytes -> ML (rand_state & leaf_package_t bytes)
let gen_leaf_package #bytes #cb rng secrets sign_pk hpke_pk =
  let (rng, identity) = gen_rand_bytes #bytes rng 8 in
  let identity: bytes = (identity <: bytes) in
  let extensions: bytes = (
    let versions = Seq.seq_of_list [PV_mls10 ()] in
    let ciphersuite_network = available_ciphersuite_to_network (ciphersuite #bytes) in
    let ciphersuites = Seq.seq_of_list [ciphersuite_network] in
    let extensions = Seq.seq_of_list [ET_capabilities (); ET_lifetime (); (* ET_key_id (); *) ET_parent_hash ()] in
    if not (bytes_length #bytes ps_protocol_version_nt (Seq.seq_to_list versions) < 256) then failwith ""
    else if not (bytes_length #bytes ps_extension_type_nt (Seq.seq_to_list extensions) < 256) then failwith ""
    else if not (bytes_length #bytes ps_cipher_suite_nt (Seq.seq_to_list ciphersuites) < 256) then failwith ""
    else (
      let ext = empty_extensions in
      let ext = extract_result (set_capabilities_extension ext ({versions; ciphersuites; extensions})) in
      let ext = extract_result (set_lifetime_extension ext ({not_before = 0; not_after = 0})) in
      ext
    )
  ) in
  let unsigned_leaf_package: leaf_package_t bytes = {
    credential = {
      version = 0;
      identity;
      signature_key = sign_pk;
    };
    endpoint_id = empty;
    version = 0;
    content = {
      content = (ps_to_pse ps_treekem_content_nt).serialize_exact ({public_key = hpke_pk});
      impl_data = empty;
    };
    extensions;
    signature = empty;
  } in
  let (rng, sign_nonce) = gen_rand_bytes rng (sign_nonce_length #bytes) in
  let signature = extract_result (
    unsigned_key_package <-- treesync_to_keypackage unsigned_leaf_package;
    let tbs = (ps_to_pse ps_key_package_tbs_nt).serialize_exact unsigned_key_package.tbs in
    sign_sign secrets.sign_sk tbs sign_nonce
  ) in
  (rng, { unsigned_leaf_package with signature })
#pop-options

val create_participant: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> ML (rand_state & leaf_package_t bytes & participant_secrets bytes)
let create_participant #bytes #cb rng =
  let (rng, sign_seed) = gen_rand_bytes rng (sign_private_key_length #bytes) in
  let (rng, leaf_secret) = gen_rand_bytes rng (hpke_private_key_length #bytes) in
  let (sign_pk, sign_sk) = extract_result (sign_gen_keypair sign_seed) in
  let (hpke_sk, hpke_pk) = extract_result (derive_keypair_from_path_secret leaf_secret) in
  let my_secrets = {sign_sk; leaf_secret} in
  let (rng, leaf_package) = gen_leaf_package rng my_secrets sign_pk hpke_pk in
  (rng, leaf_package, my_secrets)

val add_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let add_rand #bytes #cb rng st =
  let (rng, leaf_package, my_secrets) = create_participant rng in
  let (new_public_state, leaf_index) = MLS.TreeSync.add st.public leaf_package in
  (rng, {
    public = new_public_state;
    secrets = (leaf_index, my_secrets) :: st.secrets;
  })

//TODO: the group context is replaced with only the tree hash
#push-options "--z3rlimit 50 --ifuel 1 --fuel 0"
val update_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> nat -> ML (rand_state & mls_state bytes)
let update_leaf #bytes #cb rng st leaf_index =
  let leaf_secrets = get_secret st.secrets leaf_index in
  if not (leaf_index < st.public.treesize) then failwith "" else
  let tree_ts = st.public.tree in
  let tree_tk = extract_result (treesync_to_treekem tree_ts) in
  let (rng, new_leaf_secret) = gen_rand_bytes rng (hpke_private_key_length #bytes) in
  let ad = extract_result (tree_hash tree_ts) in
  let rand_length = (update_path_entropy_lengths tree_tk leaf_index) in
  //if not (rand_length < Lib.IntTypes.max_size_t) then failwith "" else
  let (rng, rand) = gen_rand_randomness rng rand_length in
  let (path_tk, _) = extract_result (update_path tree_tk leaf_index new_leaf_secret ad rand) in
  let leaf_package =
    match get_leaf tree_ts leaf_index with
    | Some lp -> lp
    | _ -> failwith ""
  in
  let ext_path_ts = extract_result (treekem_to_treesync leaf_package path_tk) in
  let (rng, sign_nonce_bytes) = gen_rand_bytes rng (sign_nonce_length #bytes) in
  let sign_nonce = sign_nonce_bytes in
  let path_ts = extract_result (external_pathsync_to_pathsync (Some (leaf_secrets.sign_sk, sign_nonce)) tree_ts ext_path_ts) in
  let new_tree_ts = apply_path tree_ts path_ts in
  (rng, {
    public = {
      st.public with
      tree = new_tree_ts;
      version = st.public.version + 1;
    };
    secrets = update_secret st.secrets (leaf_index, {leaf_secrets with leaf_secret = new_leaf_secret});
  })
#pop-options

val update_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let update_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.secrets) in
  let (leaf_index, _) = List.Tot.index st.secrets i in
  update_leaf rng st leaf_index

val remove_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> nat -> ML (rand_state & mls_state bytes)
let remove_leaf #bytes #cb rng st leaf_index =
  if not (leaf_index < st.public.treesize) then failwith "" else
  (rng, {
    public = remove st.public leaf_index;
    secrets = List.Tot.filter (fun (x, _) -> x <> leaf_index) st.secrets;
  })

val remove_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let remove_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.secrets) in
  let (leaf_index, _) = List.Tot.index st.secrets i in
  remove_leaf rng st leaf_index

#push-options "--fuel 0 --ifuel 1"
val apply_random_operation: #bytes:Type0 -> {|crypto_bytes bytes|} -> state bytes -> ML (state bytes & bool)
let apply_random_operation #bytes #cb st =
  let rng = st.rng in
  let (rng, op) =
    if 2 <= List.Tot.length st.mls.secrets then (
      let (rng, choice) = gen_rand_num_ml rng (st.test.n_add + st.test.n_update + st.test.n_remove) in
      (rng, (
        if choice < st.test.n_add then Add
        else if choice < st.test.n_add + st.test.n_update then Update
        else Remove
      ))
    ) else (
      let (rng, choice) = gen_rand_num_ml rng (st.test.n_add + st.test.n_update) in
      (rng, (
        if choice < st.test.n_add then Add
        else Update
      ))
    )
  in
  //assert (op == Add ==> 0 < st.test.n_add);
  //assert (op == Update ==> 0 < st.test.n_update);
  //assert (op == Remove ==> 0 < st.test.n_remove);
  match op with
  | Add -> (
    let (rng, mls) = add_rand rng st.mls in
    ({rng; mls; test={st.test with n_add = st.test.n_add - 1}}, false)
  )
  | Update -> (
    let (rng, mls) = update_rand rng st.mls in
    ({rng; mls; test={st.test with n_update = st.test.n_update - 1}}, true)
  )
  | Remove -> (
    let (rng, mls) = remove_rand rng st.mls in
    ({rng; mls; test={st.test with n_remove = st.test.n_remove - 1}}, false)
  )
#pop-options

#push-options "--fuel 0 --ifuel 1"
val check_root_secret: {|crypto_bytes bytes|} -> mls_state bytes -> ML unit
let check_root_secret #cb st =
  let open MLS.TreeKEM.Types in
  let (first_index, first_secret) = List.hd st.secrets in
  let tree_tk = extract_result (treesync_to_treekem st.public.tree) in
  //IO.print_string (
  //  print_tree
  //    (fun leaf -> match leaf with
  //      | None -> "_"
  //      | Some _ -> "L")
  //    (fun node -> match node with
  //      | None -> "_"
  //      | Some np -> "N[" ^ list_to_string nat_to_string np.unmerged_leaves ^ ", " ^ (if np.path_secret_from = Left then "Left" else "Right") ^ ", " ^ nat_to_string (List.Tot.length np.path_secret_ciphertext) ^ "]")
  //    tree_tk
  //);
  //IO.print_string "\n";
  if not (first_index < st.public.treesize) then failwith "" else
  let first_root_secret = extract_result (root_secret tree_tk first_index first_secret.leaf_secret) in
  List.iter #(nat & participant_secrets bytes) (fun (index, secret) ->
    if not (index < st.public.treesize) then failwith "" else
    let cur_root_secret = extract_result (root_secret tree_tk index secret.leaf_secret) in
    if not (first_root_secret = cur_root_secret) then
      failwith ("check_root_secret: " ^ nat_to_string first_index ^ " has " ^ bytes_to_hex_string first_root_secret ^ ", " ^ nat_to_string index ^ " has " ^ bytes_to_hex_string cur_root_secret)
    else
      ()
  ) (List.tail st.secrets)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val foldn: #a:Type -> nat -> (a -> ML a) -> a -> ML a
let rec foldn nb f x =
  if nb = 0 then (
    x)
  else (
    foldn (nb-1) f (f x)
  )
#pop-options

val create_init_state: #bytes:Type0 -> {|crypto_bytes bytes|} -> nat -> ML (rand_state & mls_state bytes)
let create_init_state #bytes #cb seed =
  let rng = init_rand_state seed in
  let (rng, _) = gen_rand_bytes #bytes rng 64 in // Avoid the first bad number generation (might not be useful, but doesn't hurt)
  let (rng, group_id) = gen_rand_bytes #bytes rng 16 in
  let (rng, first_leaf_package, first_secrets) = create_participant rng in
  (rng, ({
    public = create group_id first_leaf_package;
    secrets = [(0, first_secrets)];
  }))

#push-options "--fuel 0 --ifuel 1"
val run_one_self_treekem_test: {|crypto_bytes bytes|} -> nat -> nat -> nat -> nat -> ML unit
let run_one_self_treekem_test #cb seed avg_n_participant n_remove n_update =
  IO.print_string ("Running treekem tests with parameters " ^
    "seed=" ^ (nat_to_string seed) ^ ", " ^
    "avg_n_participant=" ^ (nat_to_string avg_n_participant) ^ ", " ^
    "n_remove=" ^ (nat_to_string n_remove) ^ ", " ^
    "n_update=" ^ (nat_to_string n_update) ^ "\n"
  );
  let (rng, mls) = create_init_state seed in
  let init_state = {
    rng;
    mls;
    test = {
      n_add = avg_n_participant + n_remove;
      n_update;
      n_remove;
    };
  } in
  let (_: state bytes) = foldn (avg_n_participant + n_remove + n_update + n_remove) (fun st ->
    let (st, check) = apply_random_operation st in
    (if check then check_root_secret st.mls else ());
    st
  ) init_state in
  ()
#pop-options

val custom_test_1: {|crypto_bytes bytes|} -> ML unit
let custom_test_1 #cb =
  let (rng, st) = create_init_state 0 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = update_leaf rng st 2 in
  let (rng, st) = update_leaf rng st 3 in
  let (rng, st) = update_leaf rng st 4 in
  let (rng, st) = remove_leaf rng st 2 in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 4 in
  check_root_secret st

val run_self_treekem_test: unit -> ML unit
let run_self_treekem_test () =
  let cb = mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 in
  custom_test_1 #cb;
  //                           seed add remove update
  run_one_self_treekem_test #cb 0    5   5      5   ;
  run_one_self_treekem_test #cb 1    5   20     20  ;
  run_one_self_treekem_test #cb 2    5   50     25  ;
  run_one_self_treekem_test #cb 3    10  10     10  ;
  run_one_self_treekem_test #cb 4    10  25     25   ;
  run_one_self_treekem_test #cb 5    10  50     25  ;
  run_one_self_treekem_test #cb 6    25  25     25  ;
  run_one_self_treekem_test #cb 7    50  20     100 ;
  ()
