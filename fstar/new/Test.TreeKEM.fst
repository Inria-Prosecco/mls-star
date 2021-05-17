module Test.TreeKEM

open FStar.IO
open FStar.All
open Test.Types
open Test.Utils
open Tree
open TreeSync
open TreeSync.Hash
open TreeKEM
open TreeSyncTreeKEMBinder
open NetworkTypes
open Parser
open Lib.Result
open Test.Utils
open Lib.ByteSequence
open Crypto

module TreeMath = TreeMath

val find_my_index: #l:nat -> #n:tree_size l -> treesync l n -> key_package_nt -> ML (res:nat{res<n})
let find_my_index #l #n t kp =
  let my_signature_key =
    match kp.kpn_credential with
    | C_basic c -> secret_to_pub c.bcn_signature_key
    | _ -> failwith "unsupported credential!"; bytes_empty
  in
  let test (oc: option credential_t) =
    match oc with
    | None -> false
    | Some c -> c.cred_signature_key = my_signature_key
  in
  let res = extract_option "couldn't find my_index" (find_first test (Seq.seq_to_list (tree_membership t))) in
  res

val gen_treekem_output: ciphersuite -> treekem_test_input -> ML treekem_test_output
let gen_treekem_output cs t =
  let ratchet_tree = extract_option "bad ratchet tree" ((ps_to_pse ps_ratchet_tree).parse_exact (hex_string_to_bytes t.ratchet_tree_before)) in
  let add_sender = FStar.UInt32.v t.add_sender in
  let my_leaf_secret = (hex_string_to_bytes t.my_leaf_secret) in
  let my_key_package = extract_option "bad key package" ((ps_to_pse ps_key_package).parse_exact (hex_string_to_bytes t.my_key_package)) in
  let my_path_secret = (hex_string_to_bytes t.my_path_secret) in
  let update_sender = FStar.UInt32.v t.update_sender in
  let update_path = extract_option "bad update path" ((ps_to_pse ps_update_path).parse_exact (hex_string_to_bytes t.update_path)) in
  let update_group_context = hex_string_to_bytes t.update_group_context in
  let (|l, n|) = extract_result (ratchet_tree_l_n ratchet_tree) in
  let ts0 = extract_result (ratchet_tree_to_treesync l n ratchet_tree) in
  let tk0 = extract_result (treesync_to_treekem cs ts0) in
  let my_index = find_my_index ts0 my_key_package in
  if not (my_index <> add_sender) then
    failwith ("new leaf cannot be equal to add_sender: my_index=" ^ nat_to_string my_index ^ " add_sender=" ^ nat_to_string add_sender ^ "\n")
  else if not (add_sender < n) then
    failwith "add_sender is too big"
  else if not (update_sender < n) then
    failwith "update_sender is too big"
  else (
    let tree_hash_before = extract_result (tree_hash cs (TreeMath.root l) ts0) in
    let upk0 = extract_result (mk_init_path tk0 my_index add_sender my_path_secret bytes_empty) in
    let old_leaf_package = extract_result (key_package_to_treesync my_key_package) in
    let ups0 = extract_result (treekem_to_treesync old_leaf_package upk0) in
    let ts1 = apply_path dumb_credential ts0 ups0 in
    let tk1 = extract_result (treesync_to_treekem cs ts1) in
    let root_secret_after_add = extract_result (root_secret tk1 my_index my_leaf_secret) in
    let upk1 = extract_result (update_path_to_treekem cs l n update_sender update_group_context update_path) in
    let update_leaf_package = extract_option "leaf package for update sender is empty" (snd (get_leaf ts1 update_sender)) in
    let ups1 = extract_result (treekem_to_treesync update_leaf_package upk1) in
    let ts2 = apply_path dumb_credential ts1 ups1 in
    let tk2 = extract_result (treesync_to_treekem cs ts2) in
    let root_secret_after_update = extract_result (root_secret tk2 my_index my_leaf_secret) in
    {
      tree_hash_before = bytes_to_hex_string tree_hash_before;
      root_secret_after_add = bytes_to_hex_string root_secret_after_add;
      root_secret_after_update = bytes_to_hex_string root_secret_after_update;
      ratchet_tree_after = "";
      tree_hash_after = "";
    }
  )

val test_treekem_one: treekem_test -> ML bool
let test_treekem_one t =
  if FStar.UInt16.v t.tk_cipher_suite <> 3 then (
    IO.print_string "Skipping test because only Chacha20Poly1305 is supported\n";
    true
  ) else
  match uint16_to_ciphersuite t.tk_cipher_suite with
  | Error s -> begin
    IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
    true
  end
  | Success cs -> begin
    let our_output = gen_treekem_output cs t.tk_input in
    let tree_hash_before_ok = check_equal "tree_hash_before_ok" string_to_string t.tk_output.tree_hash_before our_output.tree_hash_before in
    let root_secret_after_add_ok = check_equal "root_secret_after_add" string_to_string t.tk_output.root_secret_after_add our_output.root_secret_after_add in
    let root_secret_after_update_ok = check_equal "root_secret_after_update" string_to_string t.tk_output.root_secret_after_update our_output.root_secret_after_update in
    tree_hash_before_ok && root_secret_after_add_ok && root_secret_after_update_ok
  end

val test_treekem: list treekem_test -> ML bool
let test_treekem =
  test_list "TreeKEM" test_treekem_one
