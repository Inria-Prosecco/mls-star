module MLS.Test.FromExt.TreeKEM

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.TreeMath.Internal
open MLS.Tree
open MLS.TreeSync.TreeHash
open MLS.TreeSyncTreeKEMBinder
open MLS.NetworkBinder
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.API.Types
open MLS.TreeSync.API
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.Types
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.API
open MLS.Result
open MLS.StringUtils
open MLS.Utils
open MLS.Crypto

#set-options "--z3rlimit 100"

type participant_state {|crypto_bytes bytes|} = {
  leaf_ind: nat;
  state: treekem_state bytes leaf_ind;
  signature_key: bytes;
}

val set_path_secret: {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> bytes -> nat -> treekem bytes l i -> treekem_priv bytes l i li -> ML (treekem_priv bytes l i li)
let rec set_path_secret #cb #l #i #li path_secret height t p =
  if height > l then
    failwith "set_path_secret: bad height"
  else
    match t, p with
    | TLeaf _, PLeaf _ -> failwith "set_path_secret: height = 0"
    | TNode content _ _, PNode priv p_next ->
      if height = l then (
        let (sk, pk) = extract_result (MLS.TreeKEM.Operations.derive_keypair_from_path_secret path_secret) in
        if not (Some? content && (Some?.v content).public_key = pk) then
          failwith "set_path_secret: bad public key"
        else
          PNode (Some sk) p_next
      ) else (
        let (child, _) = get_child_sibling t li in
        PNode priv (set_path_secret path_secret height child p_next)
      )

val get_leaf_treekem_state: {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l 0 -> treekem_leaf_private -> ML participant_state
let get_leaf_treekem_state #cb #l tree leaf_priv =
  let leaf_ind = UInt32.v leaf_priv.index in
  if not (leaf_ind < pow2 l) then failwith "get_leaf_treekem_state: leaf_ind too big";
  let encryption_priv = extract_result (mk_hpke_private_key (hex_string_to_bytes leaf_priv.encryption_priv) "get_leaf_treekem_state" "encryption_priv") in
  let priv = List.fold_right (fun path_secret priv -> set_path_secret (hex_string_to_bytes path_secret.path_secret) (level (UInt32.v path_secret.node)) tree priv) leaf_priv.path_secrets (MLS.TreeKEM.Operations.create_empty_priv encryption_priv) in
  assume(MLS.TreeKEM.Invariants.treekem_invariant tree);
  assume(MLS.TreeKEM.Invariants.treekem_priv_invariant tree priv);
  {
    leaf_ind;
    state = {
      levels = l;
      tree;
      priv;
    };
    signature_key = hex_string_to_bytes leaf_priv.signature_priv;
  }

val check_one_update_path: {|crypto_bytes bytes|} -> #l:nat -> #li:leaf_index l 0 -> group_context_nt bytes -> treesync bytes tkt l 0 -> pathkem bytes l 0 li -> bytes -> list (option string) -> participant_state -> ML unit
let check_one_update_path #cb #l #li group_context tsync treekem_path expected_commit_secret expected_opt_path_secrets st =
  if li = st.leaf_ind then (
    if not (List.nth expected_opt_path_secrets st.leaf_ind = None) then failwith "check_one_update_path: path_secret should be null"
  ) else (
    let expected_opt_path_secret = List.nth expected_opt_path_secrets st.leaf_ind in
    if not (l = st.state.levels) then failwith "check_one_update_path: bad levels";
    if not (Some? (expected_opt_path_secret)) then failwith "check_one_update_path: path_secret should be non-null";
    if not (MLS.TreeKEM.Operations.check_update_path_ciphertexts_lengthes st.state.tree treekem_path) then failwith "check_one_update_path: bad ciphertext lengthes";
    let Some expected_path_secret = expected_opt_path_secret in
    let expected_path_secret = hex_string_to_bytes expected_path_secret in
    assume(MLS.TreeKEM.Invariants.path_filtering_weak_ok st.state.tree treekem_path);
    let (path_secret, least_common_ancestor_level) = extract_result (MLS.TreeKEM.Operations.get_path_secret st.state.tree st.state.priv treekem_path group_context) in
    let new_tree = MLS.TreeKEM.Operations.tree_apply_path st.state.tree treekem_path in
    let (_, commit_secret) = extract_result (MLS.TreeKEM.Operations.path_apply_path new_tree st.state.priv path_secret least_common_ancestor_level) in
    check_equal "path_secret" (bytes_to_hex_string) expected_path_secret path_secret;
    check_equal "commit_secret" (bytes_to_hex_string) expected_commit_secret commit_secret
  )

val check_update_path: {|crypto_bytes bytes|} -> #l:nat -> group_context_nt bytes -> treesync bytes tkt l 0 -> list participant_state -> treekem_update_path -> ML unit
let check_update_path #cb #l group_context tsync treekem_states t =
  let sender = UInt32.v t.sender in
  let commit_secret = hex_string_to_bytes t.commit_secret in
  if not (sender < pow2 l) then failwith "check_update_path: sender too big";
  let update_path = extract_option "update_path" ((ps_prefix_to_ps_whole ps_update_path_nt).parse (hex_string_to_bytes t.update_path)) in
  let uncompressed_path = extract_result (uncompress_update_path sender tsync update_path) in
  let treesync_path = update_path_to_treesync uncompressed_path in
  let treekem_path = update_path_to_treekem uncompressed_path in
  let tsync_after: treesync bytes tkt l 0 = if not (MLS.TreeSync.Operations.apply_path_pre tsync treesync_path) then failwith "check_update_path: bad apply_path pre" else MLS.TreeSync.Operations.apply_path tsync treesync_path in
  let tree_hash_after = if not (tree_hash_pre tsync_after) then failwith "check_update_path: bad tree hash pre" else tree_hash tsync_after in
  let group_context = { group_context with tree_hash = tree_hash_after; } in
  if not (MLS.TreeSync.Operations.apply_path_pre tsync treesync_path) then failwith "check_update_path: bad apply_path precondition";
  if not (MLS.TreeSync.Operations.path_is_valid group_context.group_id tsync treesync_path) then failwith "check_update_path: invalid path";
  List.iter (check_one_update_path group_context tsync treekem_path commit_secret t.path_secrets) treekem_states;
  List.iteri (fun i opt_path_secret ->
    if not (0 <= i && i < pow2 l) then failwith "check_update_path: bad i";
    if not ((i = sender || leaf_at tsync i = None) = (opt_path_secret = None)) then failwith "check_update_path: incoherent null path secret"
  ) t.path_secrets;
  check_equal "tree_hash_after" (bytes_to_hex_string) (hex_string_to_bytes t.tree_hash_after) tree_hash_after

val generate_my_update_path: {|crypto_bytes bytes|} -> #l:nat -> group_context_nt bytes -> treesync bytes tkt l 0 -> participant_state -> ML (update_path_nt bytes & bytes)
let generate_my_update_path #cb #l group_context tsync st =
  if not (st.leaf_ind < pow2 l) then failwith "generate_my_update_path: leaf_ind too big";
  if not (l = st.state.levels) then failwith "generate_my_update_path: bad levels";
  let rand = init_rand_state st.leaf_ind in
  let (rand, prepare_create_commit_rand) = gen_rand_randomness rand _ in
  let (rand, sign_nonce) = gen_rand_bytes rand _ in
  let signature_key = extract_result (mk_sign_private_key st.signature_key "generate_my_update_path" "signature_key") in
  let (pending_create_commit, pre_update_path) = extract_result (prepare_create_commit st.state prepare_create_commit_rand) in
  let update_path_sync = extract_result (
    let? my_new_leaf_package_data = (
      let opt_my_leaf_package = leaf_at tsync st.leaf_ind in
      let? my_leaf_package = (from_option "generate_update_path: my leaf is blanked" opt_my_leaf_package) in
      return ({
        my_leaf_package.data with
        source = LNS_update;
        lifetime = ();
        parent_hash = ();
      })
    ) in
    let? ext_update_path = treekem_to_treesync my_new_leaf_package_data pre_update_path in
    if not (MLS.TreeSync.Operations.external_path_to_path_pre tsync ext_update_path group_context.group_id) then
      error "generate_update_path: bad precondition"
    else
      return (MLS.TreeSync.Operations.external_path_to_path tsync ext_update_path group_context.group_id signature_key sign_nonce)
  ) in
  let (rand, finalize_create_commit_rand) = gen_rand_randomness rand _ in
  let create_commit_result = extract_result (MLS.TreeKEM.API.finalize_create_commit pending_create_commit [] group_context finalize_create_commit_rand) in
  let uncompressed_update_path = mls_star_paths_to_update_path update_path_sync create_commit_result.update_path in
  (extract_result (compress_update_path tsync uncompressed_update_path), create_commit_result.commit_secret)

val check_one_my_update_path: {|crypto_bytes bytes|} -> #l:nat -> group_context_nt bytes -> treesync bytes tkt l 0 -> participant_state -> nat -> update_path_nt bytes -> bytes -> ML unit
let check_one_my_update_path #cb #l group_context tsync st sender update_path expected_commit_secret =
  if not (sender < pow2 l) then failwith "check_one_my_update_path: sender too big";
  if not (l = st.state.levels) then failwith "check_one_my_update_path: bad levels";
  if sender = st.leaf_ind then () else (
    let uncompressed_path = extract_result (uncompress_update_path sender tsync update_path) in
    let treesync_path = update_path_to_treesync uncompressed_path in
    let treekem_path = update_path_to_treekem uncompressed_path in
    if not (MLS.TreeSync.Operations.path_is_valid group_context.group_id tsync treesync_path) then failwith "check_one_my_update_path: invalid path";
    assume(MLS.NetworkBinder.Properties.path_filtering_ok st.state.tree treekem_path);
    let (new_tkem_state, commit_secret) = extract_result (MLS.TreeKEM.API.commit st.state treekem_path [] group_context) in
    check_equal "commit_secret" (bytes_to_hex_string) (expected_commit_secret) (commit_secret)
  )

val check_my_update_path: {|crypto_bytes bytes|} -> #l:nat -> group_context_nt bytes -> treesync bytes tkt l 0 -> list participant_state -> ML unit
let check_my_update_path #cb #l group_context tsync states =
  List.iter (fun st_gen ->
    let (update_path, expected_commit_secret) = generate_my_update_path group_context tsync st_gen in
    List.iter (fun st_process ->
      check_one_my_update_path group_context tsync st_process st_gen.leaf_ind update_path expected_commit_secret
    ) states
  ) states

val test_treekem_one: treekem_test -> ML bool
let test_treekem_one t =
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
    let ratchet_tree = extract_option "ratchet_tree" (((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt))).parse (hex_string_to_bytes t.ratchet_tree)) in
    let (|l, tsync|) = extract_result (ratchet_tree_to_treesync ratchet_tree) in
    let tkem = extract_result (treesync_to_treekem tsync) in
    let tree_hash = if not (tree_hash_pre tsync) then failwith "test_treekem_one: bad tree hash pre" else tree_hash tsync in
    let group_context = gen_group_context (ciphersuite #bytes) (hex_string_to_bytes t.group_id) (UInt64.v t.epoch) tree_hash (hex_string_to_bytes t.confirmed_transcript_hash) in
    let states = List.map (get_leaf_treekem_state tkem) t.leaves_private in
    List.iter (check_update_path group_context tsync states) t.update_paths;
    check_my_update_path group_context tsync states;
    true
  end

val test_treekem: list treekem_test -> ML nat
let test_treekem =
  test_list "TreeKEM" test_treekem_one
