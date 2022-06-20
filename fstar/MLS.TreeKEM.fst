module MLS.TreeKEM

open Comparse.Bytes
open MLS.Crypto
open MLS.Utils
open MLS.Tree
open MLS.TreeKEM.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

val leaf_public_key: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> leaf_index l -> option (hpke_public_key bytes)
let rec leaf_public_key #bytes #cb #l t leaf_index =
  match t with
  | TLeaf None -> None
  | TLeaf (Some mi) -> Some (mi.public_key)
  | TNode _ left right ->
    let (dir, new_leaf_index) = child_index l leaf_index in
    if dir = Left then
      leaf_public_key left new_leaf_index
    else
      leaf_public_key right new_leaf_index

//This is a special case of the original_* functions below
val unmerged_leaves_resolution: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> list nat -> list (hpke_public_key bytes)
let unmerged_leaves_resolution #bytes #cb #l t indexes =
  List.Tot.concatMap (fun (index:nat) ->
    if index < pow2 l then
      match leaf_public_key t index with
      | None -> []
      | Some res -> [res]
    else
      []
  ) indexes

//This is a special case of the original_* functions below
val tree_resolution: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> list (hpke_public_key bytes)
let rec tree_resolution #bytes #cb #l t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some mi) -> [mi.public_key]
  | TNode (Some kp) left right -> (kp.public_key)::(unmerged_leaves_resolution t kp.unmerged_leaves)
  | TNode None left right -> (tree_resolution left)@(tree_resolution right)

val original_unmerged_leaves_resolution: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> list nat -> treekem bytes l -> list nat -> list (hpke_public_key bytes)
let original_unmerged_leaves_resolution #bytes #cb #l forbidden_leaves t indexes =
  List.Tot.concatMap (fun (index:nat) ->
    if index < pow2 l && not (List.Tot.mem index forbidden_leaves) then
      match leaf_public_key t index with
      | None -> []
      | Some res -> [res]
    else
      []
  ) indexes

val split_forbidden_leaves: l:pos -> list nat -> list nat & list nat
let rec split_forbidden_leaves l forbidden_leaves =
  match forbidden_leaves with
  | [] -> ([], [])
  | h::t ->
    let (res_l, res_r) = split_forbidden_leaves l t in
    if h < pow2 (l-1) then
      (h::res_l, res_r)
    else
      (res_l, (h-(pow2 (l-1)))::res_r)

val original_tree_resolution: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> list nat -> treekem bytes l -> list (hpke_public_key bytes)
let rec original_tree_resolution #bytes #cb #l forbidden_leaves t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some mi) -> if forbidden_leaves = [] then [mi.public_key] else []
  | TNode (Some kp) left right -> (kp.public_key)::(original_unmerged_leaves_resolution forbidden_leaves t kp.unmerged_leaves)
  | TNode None left right ->
    let (left_forbidden_leaves, right_forbidden_leaves) = split_forbidden_leaves l forbidden_leaves in
    (original_tree_resolution left_forbidden_leaves left)@(original_tree_resolution right_forbidden_leaves right)

val original_resolution_index: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> forbidden_leaves:list nat -> t:treekem bytes l -> leaf_index l -> nat_less (List.Tot.length (original_tree_resolution forbidden_leaves t))
let rec original_resolution_index #bytes #cb #l forbidden_leaves t leaf_index =
  match t with
  | TLeaf (Some mi) -> (
    assume (forbidden_leaves = []); //TODO: We should be able to prove it
    0
  )
  | TLeaf None -> admit() //TODO: There should be a precondition that prevent this case
  | TNode (Some kp) left right -> (
    match find_index forbidden_leaves leaf_index kp.unmerged_leaves with
    | Some res ->
      //That is currently not provable because a node might contain an unmerged leaf which is actually blanked
      assume (1+res < List.Tot.length (original_tree_resolution forbidden_leaves t));
      1+res
    | None -> 0
  )
  | TNode None left right ->
    let (child_dir, child_leaf_index) = child_index l leaf_index in
    let (child, _) = order_subtrees child_dir (left, right) in
    let (left_forbidden_leaves, right_forbidden_leaves) = split_forbidden_leaves l forbidden_leaves in
    let child_forbidden_leaves = if child_dir = Left then left_forbidden_leaves else right_forbidden_leaves in
    let child_resolution_index = original_resolution_index child_forbidden_leaves child child_leaf_index in
    List.Tot.Properties.append_length (original_tree_resolution left_forbidden_leaves left) (original_tree_resolution right_forbidden_leaves right);
    if child_dir = Left then
      child_resolution_index
    else
      (List.Tot.length (original_tree_resolution left_forbidden_leaves left)) + child_resolution_index

val hpke_multirecipient_encrypt_entropy_lengths: #bytes:Type0 -> {|crypto_bytes bytes|} -> list (hpke_public_key bytes) -> list nat
let rec hpke_multirecipient_encrypt_entropy_lengths #bytes #cb pks =
  match pks with
  | [] -> []
  | h::t -> (hpke_private_key_length #bytes)::(hpke_multirecipient_encrypt_entropy_lengths t)

val hpke_multirecipient_encrypt: #bytes:Type0 -> {|crypto_bytes bytes|} -> pks:list (hpke_public_key bytes) -> info:bytes -> ad:bytes -> plaintext:bytes -> randomness bytes (hpke_multirecipient_encrypt_entropy_lengths pks) -> result (list (path_secret_ciphertext bytes))
let rec hpke_multirecipient_encrypt #bytes #cb public_keys info ad plaintext rand =
  match public_keys with
  | [] -> return []
  | pk::pks ->
    let (rand_cur, rand_next) = dest_randomness rand in
    res_hd <-- hpke_encrypt pk info ad plaintext rand_cur;
    res_tl <-- hpke_multirecipient_encrypt pks info ad plaintext rand_next;
    return ({kem_output = fst res_hd; ciphertext = snd res_hd}::res_tl)

val derive_keypair_from_path_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (hpke_private_key bytes & hpke_public_key bytes)
let derive_keypair_from_path_secret #bytes #cb path_secret =
  node_secret <-- derive_secret path_secret (string_to_bytes #bytes "node");
  hpke_gen_keypair (node_secret <: bytes)

val derive_next_path_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result bytes
let derive_next_path_secret #bytes #cb path_secret =
  res <-- derive_secret path_secret (string_to_bytes #bytes "path");
  return (res <: bytes)

val node_encap: #bytes:Type0 -> {|crypto_bytes bytes|} -> version:nat -> child_secret:bytes -> hpke_info:bytes -> direction -> pks:list (hpke_public_key bytes) -> randomness bytes (hpke_multirecipient_encrypt_entropy_lengths pks) -> result (key_package bytes & bytes)
let node_encap #bytes #cb version child_secret hpke_info dir pks rand =
  node_secret <-- derive_next_path_secret child_secret;
  node_keys <-- derive_keypair_from_path_secret node_secret;
  ciphertext <-- hpke_multirecipient_encrypt pks hpke_info empty node_secret rand;
  return (
    {
      public_key = snd node_keys;
      version = version;
      last_group_context = hpke_info;
      unmerged_leaves = [];
      path_secret_from = dir;
      path_secret_ciphertext = ciphertext;
    },
    node_secret
  )

val node_decap: #bytes:Type0 -> {|crypto_bytes bytes|} -> child_secret:bytes -> i:nat -> dir:direction -> kp:key_package bytes{dir <> kp.path_secret_from ==> i < List.Tot.length kp.path_secret_ciphertext} -> result bytes
let node_decap #bytes #cb child_secret i dir kp =
  if dir = kp.path_secret_from then (
    if i <> 0 then
      internal_failure "node_decap"
    else
      derive_next_path_secret child_secret
  ) else (
    let ciphertext = List.Tot.index kp.path_secret_ciphertext i in
    child_keys <-- derive_keypair_from_path_secret child_secret;
    let child_sk = fst child_keys in
    hpke_decrypt ciphertext.kem_output child_sk (kp.last_group_context) empty ciphertext.ciphertext
  )

val update_path_entropy_lengths: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> leaf_index l -> list nat
let rec update_path_entropy_lengths #bytes #cb #l t leaf_index =
  match t with
  | TLeaf _ -> []
  | TNode _ left right ->
    let (dir, new_leaf_index) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    if tree_resolution sibling = [] then
      update_path_entropy_lengths child new_leaf_index
    else
      hpke_multirecipient_encrypt_entropy_lengths (tree_resolution sibling) @ update_path_entropy_lengths child new_leaf_index

val update_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> t:treekem bytes l -> leaf_index:leaf_index l -> leaf_secret:bytes -> ad:bytes -> randomness bytes (update_path_entropy_lengths t leaf_index) -> Pure (result (pathkem bytes l & bytes))
  (requires length leaf_secret >= hpke_private_key_length #bytes)
  (ensures fun res -> match res with
    | Success (_, node_secret) -> length leaf_secret >= hpke_private_key_length #bytes
    | _ -> True
  )
let rec update_path #bytes #cb #l t leaf_index leaf_secret ad rand =
  match t with
  | TLeaf None -> admit() //TODO: in the previous code, it fails in this case
  | TLeaf (Some mi) ->
    //TODO: in the previous code, it does some credential check here
    leaf_keys <-- derive_keypair_from_path_secret leaf_secret;
    return (PLeaf ({public_key=snd leaf_keys; version=mi.version+1;} <: member_info bytes), leaf_secret)
  | TNode okp left right ->
    let version =
      match okp with
      | None -> 0
      | Some kp -> kp.version+1
    in
    let (dir, next_leaf_index) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    if tree_resolution sibling = [] then (
      let next_rand: randomness bytes (update_path_entropy_lengths #_ #_ #(l-1) child next_leaf_index) = rand in
      recursive_call <-- update_path child next_leaf_index leaf_secret ad next_rand;
      let (child_path, child_path_secret) = recursive_call in
      return (PNode None child_path, child_path_secret)
    ) else (
      let (rand_cur, rand_next) = split_randomness rand in
      recursive_call <-- update_path child next_leaf_index leaf_secret ad rand_next;
      let (child_path, child_path_secret) = recursive_call in
      node_encap_call <-- node_encap version child_path_secret ad dir (tree_resolution sibling) rand_cur;
      let (node_kp, node_path_secret) = node_encap_call in
      return (PNode (Some node_kp) child_path, node_path_secret)
    )

val root_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> t:treekem bytes l -> leaf_index l -> leaf_secret:bytes -> result (bytes)
let rec root_secret #bytes #cb #l t leaf_index leaf_secret =
  match t with
  | TLeaf None -> internal_failure "root_secret: leaf_index corresponds to an empty leaf"
  | TLeaf (Some _) -> return leaf_secret
  | TNode (Some kp) left right -> begin
    if List.Tot.mem leaf_index kp.unmerged_leaves then (
      return leaf_secret
    ) else (
      let (dir, next_leaf_index) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      child_path_secret <-- root_secret child next_leaf_index leaf_secret;
      //The condition is here becaus the `i` argument has not sense when dir = kp.path_secret_from.
      //Maybe we should refactor `node_decap`?
      let (left_forbidden_leaves, right_forbidden_leaves) = split_forbidden_leaves l kp.unmerged_leaves in
      let child_forbidden_leaves = if dir = Left then left_forbidden_leaves else right_forbidden_leaves in
      let i = if dir = kp.path_secret_from then 0 else original_resolution_index child_forbidden_leaves child next_leaf_index in
      assume (dir <> kp.path_secret_from ==> List.Tot.length (original_tree_resolution child_forbidden_leaves child) == List.Tot.length kp.path_secret_ciphertext);
      node_decap child_path_secret i dir kp
    )
  end
  | TNode None left right -> begin
    let (dir, next_leaf_index) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    root_secret child next_leaf_index leaf_secret
  end

val find_least_common_ancestor: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> my_ind:leaf_index l -> other_ind:leaf_index l{my_ind <> other_ind} -> (res_l:nat & treekem bytes res_l & leaf_index res_l)
let rec find_least_common_ancestor #bytes #cb #l t my_ind other_ind =
  match t with
  | TNode _ left right ->
      let (my_dir, next_my_ind) = child_index l my_ind in
      let (other_dir, next_other_ind) = child_index l other_ind in
      if my_dir = other_dir then (
        let (child, sibling) = order_subtrees my_dir (left, right) in
        find_least_common_ancestor child next_my_ind next_other_ind
      ) else (
        (|l, t, my_ind|)
      )

val path_secret_at_least_common_ancestor: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> my_ind:leaf_index l -> other_ind:leaf_index l{my_ind <> other_ind} -> leaf_secret:bytes -> result bytes
let path_secret_at_least_common_ancestor #bytes #cb #l t my_ind other_ind leaf_secret =
  let (|_, lca, lca_my_ind|) = find_least_common_ancestor t my_ind other_ind in
  root_secret lca lca_my_ind leaf_secret

val empty_path_secret_ciphertext: #bytes:Type0 -> {|crypto_bytes bytes|} -> path_secret_ciphertext bytes
let empty_path_secret_ciphertext #bytes #cb = {
    kem_output = mk_zero_vector (hpke_kem_output_length #bytes);
    ciphertext = empty;
  }

val mk_init_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> update_index:leaf_index l -> result (pathkem bytes l)
let rec mk_init_path_aux #bytes #cb #l t update_index =
  match t with
  | TLeaf None -> error "mk_init_path_aux: update leaf cannot be blanked"
  | TLeaf (Some mi) -> return (PLeaf mi)
  | TNode okp left right -> begin
    let (update_dir, next_update_index) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    let new_okp =
      match okp with
      | Some kp -> Some ({ kp with
          path_secret_from = update_dir;
        })
      | None -> None
    in
    next <-- mk_init_path_aux child next_update_index;
    return (PNode okp next)
  end

val mk_init_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem bytes l -> my_index:leaf_index l -> update_index:leaf_index l{my_index <> update_index} -> path_secret:bytes -> hpke_info:bytes -> result (pathkem bytes l)
let rec mk_init_path #bytes #cb #l t my_index update_index path_secret hpke_info =
  match t with
  | TNode okp left right -> begin
    let (my_dir, next_my_index) = child_index l my_index in
    let (update_dir, next_update_index) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    if my_dir = update_dir then (
      let new_okp =
        match okp with
        | Some kp -> Some ({ kp with
          path_secret_from = update_dir;
        })
        | None -> None
      in
      next <-- mk_init_path child next_my_index next_update_index path_secret hpke_info;
      return (PNode new_okp next)
    ) else (
      if not (Some? okp && (Some?.v okp).unmerged_leaves = []) then
        error "mk_init_path: the lowest common ancestor must be non-blank and have empty unmerged leaves"
      else (
        let kp = Some?.v okp in
        let resol_size = List.Tot.length (original_tree_resolution [] sibling) in
        let resol_index = original_resolution_index [] sibling next_my_index in
        let fake_randomness = mk_zero_vector (hpke_private_key_length #bytes) in
        my_pk <-- from_option "leaf at my_index is empty!" (leaf_public_key t my_index);
        my_path_secret_ciphertext <-- hpke_encrypt my_pk hpke_info empty path_secret fake_randomness;
        let new_kp = { kp with
          path_secret_from = update_dir;
          last_group_context = hpke_info;
          //TODO: put the {kem_output = ...; ...} in a separate function
          path_secret_ciphertext = Seq.seq_to_list (Seq.upd (Seq.create resol_size (empty_path_secret_ciphertext)) resol_index ({kem_output=fst my_path_secret_ciphertext; ciphertext = snd my_path_secret_ciphertext}));
        } in
        next <-- mk_init_path_aux child next_update_index;
        return (PNode (Some new_kp) next)
      )
    )
  end
