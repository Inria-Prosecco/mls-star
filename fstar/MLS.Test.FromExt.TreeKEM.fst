module MLS.Test.FromExt.TreeKEM

open FStar.IO
open FStar.All
open MLS.Test.Types
open MLS.Test.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.TreeSync.ExternalPath
open MLS.TreeSync
open MLS.TreeSync.Hash
open MLS.TreeKEM
open MLS.TreeSyncTreeKEMBinder
open MLS.NetworkBinder
open MLS.NetworkTypes
open MLS.Parser
open MLS.Result
open MLS.StringUtils
open MLS.Test.Utils
open Lib.ByteSequence
open MLS.Crypto
open MLS.TreeSync.IntegrityCheck

val leaf_integrity_error_to_string: leaf_integrity_error -> string
let leaf_integrity_error_to_string err =
  match err with
  | LIE_BadSignature -> "BadSignature"
  | LIE_NoCapabilities -> "NoCapabilities"
  | LIE_ExtensionsNotInCapabilities -> "ExtensionsNotInCapabilities"
  | LIE_NoLifetime -> "NoLifetime"

val node_integrity_error_to_string: node_integrity_error -> string
let node_integrity_error_to_string err =
  match err with
  | NIE_BadParentHash -> "BadParentHash"

val integrity_error_to_string: integrity_error -> string
let integrity_error_to_string ie =
  match ie with
  | IE_LeafError err ind ->
    leaf_integrity_error_to_string err ^ " " ^ nat_to_string ind
  | IE_NodeError err left lev ->
    node_integrity_error_to_string err ^ " " ^ nat_to_string left ^ " " ^ nat_to_string lev

val find_my_index: #l:nat -> #n:tree_size l -> treesync l n -> key_package_nt -> ML (res:nat{res<n})
let find_my_index #l #n t kp =
  let my_signature_key =
    match kp.credential with
    | C_basic c -> secret_to_pub c.signature_key
    | _ -> failwith "unsupported credential!"; bytes_empty
  in
  let test (oc: option credential_t) =
    match oc with
    | None -> false
    | Some c -> c.signature_key = my_signature_key
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
  let ts0_valid = extract_result (check_treesync cs ts0) in
  (
    match ts0_valid with
    | IE_Good -> ()
    | IE_Errors lerr -> IO.print_string ("ratchet_tree_before is not valid: " ^ list_to_string integrity_error_to_string lerr ^ "\n")
  );
  let tk0 = extract_result (treesync_to_treekem cs ts0) in
  let my_index = find_my_index ts0 my_key_package in
  if not (my_index <> add_sender) then
    failwith ("new leaf cannot be equal to add_sender: my_index=" ^ nat_to_string my_index ^ " add_sender=" ^ nat_to_string add_sender ^ "\n")
  else if not (add_sender < n) then
    failwith "add_sender is too big"
  else if not (update_sender < n) then
    failwith "update_sender is too big"
  else (
    let tree_hash_before = extract_result (tree_hash cs (MLS.TreeMath.root l) ts0) in
    let upk0 = extract_result (mk_init_path tk0 my_index add_sender my_path_secret bytes_empty) in
    let old_leaf_package = extract_option "leaf package for add sender is empty" (snd (get_leaf ts0 add_sender)) in
    let ext_ups0 = extract_result (treekem_to_treesync old_leaf_package upk0) in
    let ups0 = extract_result (external_pathsync_to_pathsync cs None ts0 ext_ups0) in
    let ts1 = apply_path dumb_credential ts0 ups0 in
    let tk1 = extract_result (treesync_to_treekem cs ts1) in
    let root_secret_after_add = extract_result (root_secret tk1 my_index my_leaf_secret) in
    let upk1 = extract_result (update_path_to_treekem cs l n update_sender update_group_context update_path) in

    let update_leaf_package = extract_result (key_package_to_treesync update_path.leaf_key_package) in
    let ext_ups1 = extract_result (treekem_to_treesync update_leaf_package upk1) in
    let ups1 = extract_result (external_pathsync_to_pathsync cs None ts1 ext_ups1) in
    let ts2 = apply_path dumb_credential ts1 ups1 in
    let tk2 = extract_result (treesync_to_treekem cs ts2) in

    let root_secret_after_update = extract_result (root_secret tk2 my_index my_leaf_secret) in

    let ratchet_tree2 = extract_result (treesync_to_ratchet_tree cs ts2) in
    let byte_length_ratchet_tree2 = byte_length (ps_option ps_node) (Seq.seq_to_list ratchet_tree2) in
    let ratchet_tree_after = if 1 <= byte_length_ratchet_tree2 && byte_length_ratchet_tree2 < pow2 32 then ps_ratchet_tree.serialize ratchet_tree2 else bytes_empty in
    let tree_hash_after = extract_result (tree_hash cs (MLS.TreeMath.root l) ts2) in
    {
      tree_hash_before = bytes_to_hex_string tree_hash_before;
      root_secret_after_add = bytes_to_hex_string root_secret_after_add;
      root_secret_after_update = bytes_to_hex_string root_secret_after_update;
      ratchet_tree_after = bytes_to_hex_string ratchet_tree_after;
      tree_hash_after = bytes_to_hex_string tree_hash_after;
    }
  )

val test_treekem_one: treekem_test -> ML bool
let test_treekem_one t =
  if FStar.UInt16.v t.cipher_suite <> 3 then (
    IO.print_string "Skipping test because only Chacha20Poly1305 is supported\n";
    true
  ) else
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
    let sanitize_hash h = if String.length h = 66 then String.sub h 2 64 else h in
    let input = {t.input with
      my_leaf_secret = sanitize_hash t.input.my_leaf_secret;
      my_path_secret = sanitize_hash t.input.my_path_secret;
    } in
    let output = {t.output with
      root_secret_after_add = sanitize_hash t.output.root_secret_after_add;
      root_secret_after_update = sanitize_hash t.output.root_secret_after_update;
    } in
    let t = {t with
      input = input;
      output = output;
    } in
    let our_output = gen_treekem_output cs t.input in
    let tree_hash_before_ok = check_equal "tree_hash_before_ok" string_to_string t.output.tree_hash_before our_output.tree_hash_before in
    let root_secret_after_add_ok = check_equal "root_secret_after_add" string_to_string t.output.root_secret_after_add our_output.root_secret_after_add in
    let root_secret_after_update_ok = check_equal "root_secret_after_update" string_to_string t.output.root_secret_after_update our_output.root_secret_after_update in
    let ratchet_tree_after_ok = check_equal "ratchet_tree_after" string_to_string t.output.ratchet_tree_after our_output.ratchet_tree_after in
    let tree_hash_after_ok = check_equal "tree_hash_after" string_to_string t.output.tree_hash_after our_output.tree_hash_after in
    tree_hash_before_ok && root_secret_after_add_ok && root_secret_after_update_ok && ratchet_tree_after_ok && tree_hash_after_ok
  end

val test_treekem: list treekem_test -> ML bool
let test_treekem =
  test_list "TreeKEM" test_treekem_one
