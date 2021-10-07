module MLS.TreeKEM

open MLS.Crypto
open MLS.Utils
open MLS.Tree
open Lib.ByteSequence
open Lib.IntTypes
open MLS.TreeKEM.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let todo_bytes = bytes_empty

val leaf_public_key: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> leaf_index n -> option (hpke_public_key cs)
let rec leaf_public_key #cs #l #n t leaf_index =
  match t with
  | TLeaf None -> None
  | TLeaf (Some mi) -> Some (mi.public_key)
  | TSkip _ t' -> leaf_public_key t' leaf_index
  | TNode _ left right ->
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    if dir = Left then
      leaf_public_key left new_leaf_index
    else
      leaf_public_key right new_leaf_index

val unmerged_leafs_resolution: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> list nat -> list (hpke_public_key cs)
let unmerged_leafs_resolution #cs #l #n t indexes =
  List.Tot.concatMap (fun (index:nat) ->
    if index < n then
      match leaf_public_key t index with
      | None -> []
      | Some res -> [res]
    else
      []
  ) indexes

val tree_resolution: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> list (hpke_public_key cs)
let rec tree_resolution #cs #l t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some mi) -> [mi.public_key]
  | TSkip _ t' -> tree_resolution t'
  | TNode (Some kp) left right -> (kp.public_key)::(unmerged_leafs_resolution t kp.unmerged_leafs)
  | TNode None left right -> (tree_resolution left)@(tree_resolution right)

val resolution_index: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> t:treekem cs l n -> leaf_index n -> nat_less (List.Tot.length (tree_resolution t))
let rec resolution_index #cs #l t leaf_index =
  match t with
  | TLeaf (Some mi) -> 0
  | TLeaf None -> admit() //There should be a precondition that prevent this case
  | TSkip _ t' -> resolution_index t' leaf_index
  | TNode (Some kp) left right -> (
    match find_index leaf_index kp.unmerged_leafs with
    | Some res ->
      //That is currently not true because a node can contain an unmerged leaf which is actually blanked
      assume (1+res < List.Tot.length (tree_resolution t));
      1+res
    | None -> 0
  )
  | TNode None left right ->
    let (|child_dir, child_leaf_index|) = child_index l leaf_index in
    let (child, _) = order_subtrees child_dir (left, right) in
    let child_resolution_index = resolution_index child child_leaf_index in
    List.Tot.Properties.append_length (tree_resolution left) (tree_resolution right);
    if child_dir = Left then
      child_resolution_index
    else
      (List.Tot.length (tree_resolution left)) +child_resolution_index

val hpke_multirecipient_encrypt_entropy_length: #cs:ciphersuite -> list (hpke_public_key cs) -> nat
let hpke_multirecipient_encrypt_entropy_length #cs pks =
  let open FStar.Mul in
  (List.Tot.length pks) * (hpke_private_key_length cs)

val hpke_multirecipient_encrypt: #cs:ciphersuite -> pks:list (hpke_public_key cs) -> info:bytes -> ad:bytes -> plaintext:bytes -> randomness (hpke_multirecipient_encrypt_entropy_length pks) -> result (list (path_secret_ciphertext cs))
let rec hpke_multirecipient_encrypt #cs public_keys info ad plaintext rand =
  match public_keys with
  | [] -> return []
  | pk::pks ->
    let (rand_next, rand_cur) = split_randomness rand (hpke_private_key_length cs) in
    res_hd <-- hpke_encrypt cs pk info ad plaintext rand_cur;
    res_tl <-- hpke_multirecipient_encrypt pks info ad plaintext rand_next;
    return ({kem_output = fst res_hd; ciphertext = snd res_hd}::res_tl)

val derive_keypair_from_path_secret: cs:ciphersuite -> bytes -> result (hpke_private_key cs & hpke_public_key cs)
let derive_keypair_from_path_secret cs path_secret =
  node_secret <-- derive_secret cs path_secret (string_to_bytes "node");
  hpke_gen_keypair cs node_secret

val derive_next_path_secret: cs:ciphersuite -> bytes -> result bytes
let derive_next_path_secret cs path_secret =
  res <-- derive_secret cs path_secret (string_to_bytes "path");
  return (res <: bytes)

val node_encap: #cs:ciphersuite -> version:nat -> child_secret:bytes -> ad:bytes -> direction -> pks:list (hpke_public_key cs) -> randomness (hpke_multirecipient_encrypt_entropy_length pks) -> result (key_package cs & bytes)
let node_encap #cs version child_secret ad dir pks rand =
  node_secret <-- derive_next_path_secret cs child_secret;
  node_keys <-- derive_keypair_from_path_secret cs node_secret;
  ciphertext <-- hpke_multirecipient_encrypt pks bytes_empty ad node_secret rand;
  return (
    {
      public_key = snd node_keys;
      version = version;
      last_group_context = ad;
      unmerged_leafs = [];
      path_secret_from = dir;
      path_secret_ciphertext = ciphertext;
    },
    node_secret
  )

val node_decap: #cs:ciphersuite -> child_secret:bytes -> i:nat -> dir:direction -> kp:key_package cs{dir <> kp.path_secret_from ==> i < List.Tot.length kp.path_secret_ciphertext} -> result bytes
let node_decap #cs child_secret i dir kp =
  if dir = kp.path_secret_from then (
    if i <> 0 then
      internal_failure "node_decap"
    else
      derive_next_path_secret cs child_secret
  ) else (
    let ciphertext = List.Tot.index kp.path_secret_ciphertext i in
    child_keys <-- derive_keypair_from_path_secret cs child_secret;
    let child_sk = fst child_keys in
    hpke_decrypt cs ciphertext.kem_output child_sk bytes_empty (kp.last_group_context) ciphertext.ciphertext
  )

val update_path_entropy_length: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> leaf_index n -> nat
let rec update_path_entropy_length #cs #l #n t leaf_index =
  match t with
  | TLeaf _ -> 0
  | TSkip _ t' -> update_path_entropy_length t' leaf_index
  | TNode _ left right ->
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    hpke_multirecipient_encrypt_entropy_length (tree_resolution sibling) + update_path_entropy_length child new_leaf_index

val update_path: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> t:treekem cs l n -> leaf_index:leaf_index n -> leaf_secret:bytes -> ad:bytes -> randomness (update_path_entropy_length t leaf_index) -> Pure (result (pathkem cs l n leaf_index & bytes))
  (requires Seq.length leaf_secret >= hpke_private_key_length cs)
  (ensures fun res -> match res with
    | Success (_, node_secret) -> Seq.length leaf_secret >= hpke_private_key_length cs
    | _ -> True
  )
let rec update_path #cs #l #n t leaf_index leaf_secret ad rand =
  match t with
  | TLeaf None -> admit() //TODO: in the previous code, it fails in this case
  | TLeaf (Some mi) ->
    //TODO: in the previous code, it does some credential check here
    leaf_keys <-- derive_keypair_from_path_secret cs leaf_secret;
    return (PLeaf ({public_key=snd leaf_keys; version=mi.version+1;} <: member_info cs), leaf_secret)
  | TSkip _ t' ->
    result <-- update_path t' leaf_index leaf_secret ad rand;
    let (result_path, result_secret) = result in
    return (PSkip _ result_path, result_secret)
  | TNode okp left right ->
    let version =
      match okp with
      | None -> 0
      | Some kp -> kp.version+1
    in
    let (|dir, next_leaf_index|) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    let (rand_next, rand_cur) = split_randomness rand (hpke_multirecipient_encrypt_entropy_length (tree_resolution sibling)) in
    recursive_call <-- update_path child next_leaf_index leaf_secret ad rand_next;
    let (child_path, child_path_secret) = recursive_call in
    node_encap_call <-- node_encap version child_path_secret ad dir (tree_resolution sibling) rand_cur;
    let (node_kp, node_path_secret) = node_encap_call in
    return (PNode node_kp child_path, node_path_secret)

val root_secret: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> t:treekem cs l n -> leaf_index n -> leaf_secret:bytes -> result (bytes)
let rec root_secret #cs #l #n t leaf_index leaf_secret =
  match t with
  | TLeaf None -> internal_failure "root_secret: leaf_index corresponds to an empty leaf"
  | TLeaf (Some _) -> return leaf_secret
  | TSkip _ t' -> root_secret t' leaf_index leaf_secret
  | TNode (Some kp) left right -> begin
    if List.Tot.mem leaf_index kp.unmerged_leafs then (
      return leaf_secret
    ) else (
      let (|dir, next_leaf_index|) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      child_path_secret <-- root_secret child next_leaf_index leaf_secret;
      //The condition is here becaus the `i` argument has not sense when dir = kp.path_secret_from.
      //Maybe we should refactor `node_decap`?
      let i = if dir = kp.path_secret_from then 0 else resolution_index child next_leaf_index in
      assume (List.Tot.length (tree_resolution child) == List.Tot.length kp.path_secret_ciphertext);
      node_decap child_path_secret i dir kp
    )
  end
  | TNode None left right -> begin
    let (|dir, next_leaf_index|) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    root_secret child next_leaf_index leaf_secret
  end

val empty_path_secret_ciphertext: cs:ciphersuite -> path_secret_ciphertext cs
let empty_path_secret_ciphertext cs = {
    kem_output = Seq.create (hpke_kem_output_length cs) (u8 0);
    ciphertext = bytes_empty;
  }

val mk_init_path_aux: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> update_index:leaf_index n -> result (pathkem cs l n update_index)
let rec mk_init_path_aux #cs #l #n t update_index =
  match t with
  | TLeaf None -> error "mk_init_path_aux: update leaf cannot be blanked"
  | TLeaf (Some mi) -> return (PLeaf mi)
  | TSkip _ t' ->
    res <-- mk_init_path_aux t' update_index;
    return (PSkip _ res)
  | TNode None left right -> begin
    error "mk_init_path_aux: path from the root to update leaf cannot contain blank node"
  end
  | TNode (Some kp) left right -> begin
    let (|update_dir, next_update_index|) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    let new_kp = { kp with
      path_secret_from = update_dir;
    } in
    next <-- mk_init_path_aux child next_update_index;
    return (PNode new_kp next)
  end

val mk_init_path: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> my_index:leaf_index n -> update_index:leaf_index n{my_index <> update_index} -> path_secret:bytes -> ad:bytes -> result (pathkem cs l n update_index)
let rec mk_init_path #cs #l #n t my_index update_index path_secret ad =
  match t with
  | TSkip _ t' ->
    res <-- mk_init_path t' my_index update_index path_secret ad;
    return (PSkip _ res)
  | TNode None left right -> begin
    error "mk_init_path: path from the root to update leaf cannot contain blank node"
  end
  | TNode (Some kp) left right -> begin
    let (|my_dir, next_my_index|) = child_index l my_index in
    let (|update_dir, next_update_index|) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    if my_dir = update_dir then (
      let new_kp = { kp with
        path_secret_from = update_dir;
      } in
      next <-- mk_init_path child next_my_index next_update_index path_secret ad;
      return (PNode new_kp next)
    ) else (
      let resol_size = List.Tot.length (tree_resolution sibling) in
      let resol_index = resolution_index sibling next_my_index in
      let fake_randomness = mk_randomness (Seq.create (hpke_private_key_length cs) (u8 0)) in
      my_pk <-- from_option "leaf at my_index is empty!" (leaf_public_key t my_index);
      my_path_secret_ciphertext <-- hpke_encrypt cs my_pk bytes_empty ad path_secret fake_randomness;
      let new_kp = { kp with
        path_secret_from = update_dir;
        last_group_context = ad;
        //TODO: put the {kem_output = ...; ...} in a separate function
        path_secret_ciphertext = Seq.seq_to_list (Seq.upd (Seq.create resol_size (empty_path_secret_ciphertext cs)) resol_index ({kem_output=fst my_path_secret_ciphertext; ciphertext = snd my_path_secret_ciphertext}));
      } in
      next <-- mk_init_path_aux child next_update_index;
      return (PNode new_kp next)
    )
  end
