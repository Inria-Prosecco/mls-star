module TreeKEM

open Crypto
open Utils
open Tree
open Lib.ByteSequence
open Lib.IntTypes
open Lib.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let todo_bytes = bytes_empty

noeq type member_info (cs:ciphersuite) = {
  mi_public_key: hpke_public_key cs;
  mi_version: nat;
}

//TODO: move this in Crypto.fsti?
noeq type path_secret_ciphertext (cs:ciphersuite) = {
  kem_output: hpke_kem_output cs;
  ciphertext: bytes;
}

noeq type key_package (cs:ciphersuite) = {
  kp_public_key: hpke_public_key cs;
  kp_version: nat;
  kp_last_group_context: bytes; //Related to version, correspond to the additional data used in the ciphertexts
  kp_unmerged_leafs: list nat;
  kp_path_secret_from: direction;
  kp_path_secret_ciphertext: list (path_secret_ciphertext cs);
}

type treekem (cs:ciphersuite) (l:nat) (n:tree_size l) = tree l n (option (member_info cs)) (option (key_package cs))
type pathkem (cs:ciphersuite) (l:nat) (n:tree_size l) (i:leaf_index n) = path l n i (member_info cs) (key_package cs)

val leaf_public_key: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> treekem cs l n -> leaf_index n -> option (hpke_public_key cs)
let rec leaf_public_key #cs #l #n t leaf_index =
  match t with
  | TLeaf None -> None
  | TLeaf (Some mi) -> Some (mi.mi_public_key)
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
  | TLeaf (Some mi) -> [mi.mi_public_key]
  | TSkip _ t' -> tree_resolution t'
  | TNode (Some kp) left right -> (kp.kp_public_key)::(unmerged_leafs_resolution t kp.kp_unmerged_leafs)
  | TNode None left right -> (tree_resolution left)@(tree_resolution right)

val resolution_index: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> t:treekem cs l n -> leaf_index n -> nat_less (List.Tot.length (tree_resolution t))
let rec resolution_index #cs #l t leaf_index =
  match t with
  | TLeaf (Some mi) -> 0
  | TLeaf None -> admit() //There should be a precondition that prevent this case
  | TSkip _ t' -> resolution_index t' leaf_index
  | TNode (Some kp) left right -> (
    match find_index leaf_index kp.kp_unmerged_leafs with
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
      kp_public_key = snd node_keys;
      kp_version = version;
      kp_last_group_context = ad;
      kp_unmerged_leafs = [];
      kp_path_secret_from = dir;
      kp_path_secret_ciphertext = ciphertext;
    },
    node_secret
  )

val node_decap: #cs:ciphersuite -> child_secret:bytes -> i:nat -> dir:direction -> kp:key_package cs{dir <> kp.kp_path_secret_from ==> i < List.Tot.length kp.kp_path_secret_ciphertext} -> result bytes
let node_decap #cs child_secret i dir kp =
  if dir = kp.kp_path_secret_from then (
    if i <> 0 then
      fail "node_decap"
    else
      derive_next_path_secret cs child_secret
  ) else (
    let ciphertext = List.Tot.index kp.kp_path_secret_ciphertext i in
    child_keys <-- derive_keypair_from_path_secret cs child_secret;
    let child_sk = fst child_keys in
    hpke_decrypt cs ciphertext.kem_output child_sk bytes_empty (kp.kp_last_group_context) ciphertext.ciphertext
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
    | Error _ -> True
    | Success (_, node_secret) -> Seq.length leaf_secret >= hpke_private_key_length cs
  )
let rec update_path #cs #l #n t leaf_index leaf_secret ad rand =
  match t with
  | TLeaf None -> admit() //TODO: in the previous code, it fails in this case
  | TLeaf (Some mi) ->
    //TODO: in the previous code, it does some credential check here
    leaf_keys <-- derive_keypair_from_path_secret cs leaf_secret;
    return (PLeaf ({mi_public_key=snd leaf_keys; mi_version=mi.mi_version+1;}), leaf_secret)
  | TSkip _ t' ->
    result <-- update_path t' leaf_index leaf_secret ad rand;
    let (result_path, result_secret) = result in
    return (PSkip _ result_path, result_secret)
  | TNode okp left right ->
    let version =
      match okp with
      | None -> 0
      | Some kp -> kp.kp_version+1
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
  | TLeaf None -> fail ""
  | TLeaf (Some _) -> return leaf_secret
  | TSkip _ t' -> root_secret t' leaf_index leaf_secret
  | TNode (Some kp) left right -> begin
    if List.Tot.mem leaf_index kp.kp_unmerged_leafs then (
      return leaf_secret
    ) else (
      let (|dir, next_leaf_index|) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      child_path_secret <-- root_secret child next_leaf_index leaf_secret;
      //The condition is here becaus the `i` argument has not sense when dir = kp.path_secret_from.
      //Maybe we should refactor `node_decap`?
      let i = if dir = kp.kp_path_secret_from then 0 else resolution_index child next_leaf_index in
      assume (List.Tot.length (tree_resolution child) == List.Tot.length kp.kp_path_secret_ciphertext);
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
  | TLeaf None -> fail "mk_init_path_aux: update leaf cannot be blanked"
  | TLeaf (Some mi) -> return (PLeaf mi)
  | TSkip _ t' ->
    res <-- mk_init_path_aux t' update_index;
    return (PSkip _ res)
  | TNode None left right -> begin
    fail "mk_init_path_aux: path from the root to update leaf cannot contain blank node"
  end
  | TNode (Some kp) left right -> begin
    let (|update_dir, next_update_index|) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    let new_kp = { kp with
      kp_path_secret_from = update_dir;
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
    fail "mk_init_path: path from the root to update leaf cannot contain blank node"
  end
  | TNode (Some kp) left right -> begin
    let (|my_dir, next_my_index|) = child_index l my_index in
    let (|update_dir, next_update_index|) = child_index l update_index in
    let (child, sibling) = order_subtrees update_dir (left, right) in
    if my_dir = update_dir then (
      let new_kp = { kp with
        kp_path_secret_from = update_dir;
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
        kp_path_secret_from = update_dir;
        kp_last_group_context = ad;
        //TODO: put the {kem_output = ...; ...} in a separate function
        kp_path_secret_ciphertext = Seq.seq_to_list (Seq.upd (Seq.create resol_size (empty_path_secret_ciphertext cs)) resol_index ({kem_output=fst my_path_secret_ciphertext; ciphertext = snd my_path_secret_ciphertext}));
      } in
      next <-- mk_init_path_aux child next_update_index;
      return (PNode new_kp next)
    )
  end

open NetworkTypes
open Parser

noeq type parent_hash_input_nt = {
  phin_public_key: hpke_public_key_nt;
  phin_parent_hash: blbytes ({min=0;max=255});
  phin_original_child_resolution: blseq hpke_public_key_nt ps_hpke_public_key ({min=0; max=(pow2 32)-1});
}

val ps_parent_hash_input: parser_serializer parent_hash_input_nt
let ps_parent_hash_input =
  isomorphism parent_hash_input_nt
    (
      _ <-- ps_hpke_public_key;
      _ <-- ps_bytes _;
      ps_seq _ ps_hpke_public_key
    )
  (fun (|public_key, (|parent_hash, original_child_resolution|)|) -> {
    phin_public_key = public_key;
    phin_parent_hash = parent_hash;
    phin_original_child_resolution = original_child_resolution;
  })
  (fun x -> (|x.phin_public_key, (|x.phin_parent_hash, x.phin_original_child_resolution|)|))

open Lib.Result

type path_parent_hash (l:nat) (n:tree_size l) (i:leaf_index n) = path l n i bytes bytes

val compute_parent_hash: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> hpke_public_key cs -> bytes -> treekem cs l n -> list (hpke_public_key cs) -> result (lbytes (hash_length cs))
let compute_parent_hash #cs #l #n public_key parent_hash sibling forbidden_public_keys =
  let sibling_resolution = tree_resolution sibling in
  let original_child_resolution = List.Tot.filter (fun pk ->
    //TODO: this should break secret independance?
    not (List.Tot.mem pk forbidden_public_keys)
  ) sibling_resolution in
  let original_child_resolution_nt = List.Tot.map (fun (x:hpke_public_key cs) -> x <: hpke_public_key_nt) original_child_resolution in
  if not (Seq.length parent_hash < 256) then
    fail "compute_parent_hash: parent_hash too long"
  else if not (byte_length ps_hpke_public_key original_child_resolution_nt < pow2 32) then
    fail "compute_parent_hash: original_child_resolution too big"
  else (
    Seq.lemma_list_seq_bij original_child_resolution_nt;
    hash_hash cs (ps_parent_hash_input.serialize ({
      phin_public_key = public_key;
      phin_parent_hash = parent_hash;
      phin_original_child_resolution = Seq.seq_of_list original_child_resolution_nt;
    }))
  )

val compute_parent_hash_path_aux: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> treekem cs l n -> pathkem cs l n i -> bytes -> result (path_parent_hash l n i)
let rec compute_parent_hash_path_aux #cs #l #n #i tree path parent_hash =
  match tree, path with
  | TLeaf _, PLeaf _ -> return (PLeaf parent_hash)
  | TSkip _ t', PSkip _ p' ->
    result <-- compute_parent_hash_path_aux t' p' parent_hash;
    return (PSkip _ result)
  | TNode tree_onp left right, PNode path_np next ->
    let (|dir, next_i|) = child_index l i in
    let (child, sibling) = order_subtrees dir (left, right) in
    let forbidden_keys =
      match tree_onp with
      | None -> []
      | Some tree_np ->
        unmerged_leafs_resolution tree tree_np.kp_unmerged_leafs
    in
    new_parent_hash <-- compute_parent_hash path_np.kp_public_key parent_hash sibling forbidden_keys;
    new_next <-- compute_parent_hash_path_aux child next new_parent_hash;
    return (PNode parent_hash new_next)

val compute_parent_hash_path: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> treekem cs l n -> pathkem cs l n i -> result (path_parent_hash l n i)
let compute_parent_hash_path #cs #l #n #i tree path =
  compute_parent_hash_path_aux tree path bytes_empty
