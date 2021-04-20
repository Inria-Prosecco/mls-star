module TreeKEM

open CryptoMLS
open NetworkTypes
open Parser
open Utils
open Lib.ByteSequence
open Lib.IntTypes
open Lib.Result

let todo_bytes = bytes_empty

type direction = | Left | Right

noeq type member_info (cs:ciphersuite) = {
  mi_public_key: hpke_public_key cs;
}

//TODO: move this in Crypto.fsti?
noeq type path_secret_ciphertext (cs:ciphersuite) = {
  kem_output: hpke_kem_output cs;
  ciphertext: bytes;
}

let index_l (l:nat) = x:nat{x < pow2 l}

noeq type key_package (cs:ciphersuite) (l:nat) = {
  kp_public_key: hpke_public_key cs;
  unmerged_leafs: list (index_l l);
  path_secret_from: direction;
  path_secret_ciphertext: list (path_secret_ciphertext cs);
}

noeq type tree (cs:ciphersuite) (lev:nat) =
  | Leaf: mi:option (member_info cs){lev=0} -> tree cs lev
  | Node: kp:option (key_package cs lev){lev>0} -> left:tree cs (lev - 1) -> right:tree cs (lev - 1) -> tree cs lev

noeq type path (cs:ciphersuite) (lev:nat) =
  | PLeaf: mi:option (member_info cs){lev=0} -> path cs lev
  | PNode: kp:option (key_package cs lev){lev>0} -> next:path cs (lev-1) -> path cs lev

let child_index (l:pos) (i:index_l l) : index_l (l-1) & direction =
  if i < pow2 (l - 1) then (i,Left) else (i-pow2 (l-1),Right)
let order_subtrees dir (l,r) = if dir = Left then (l,r) else (r,l)

val leaf_public_key: #cs:ciphersuite -> #l:nat -> tree cs l -> index_l l -> option (hpke_public_key cs)
let rec leaf_public_key #cs #l t leaf_index =
  match t with
  | Leaf None -> None
  | Leaf (Some mi) -> Some (mi.mi_public_key)
  | Node _ left right ->
    let (new_leaf_index, dir) = child_index l leaf_index in
    if dir = Left then
      leaf_public_key left new_leaf_index
    else
      leaf_public_key right new_leaf_index

val unmerged_leafs_resolution: #cs:ciphersuite -> #l:nat -> tree cs l -> list (index_l l) -> list (hpke_public_key cs)
let unmerged_leafs_resolution #cs #l t indexes =
  List.Tot.concatMap (fun index ->
    match leaf_public_key t index with
    | None -> []
    | Some res -> [res]
  ) indexes

val tree_resolution: #cs:ciphersuite -> #l:nat -> tree cs l -> list (hpke_public_key cs)
let rec tree_resolution #cs #l t =
  match t with
  | Leaf None -> []
  | Leaf (Some mi) -> [mi.mi_public_key]
  | Node (Some kp) left right -> (kp.kp_public_key)::(unmerged_leafs_resolution t kp.unmerged_leafs)
  | Node None left right -> (tree_resolution left)@(tree_resolution right)

val resolution_index: #cs:ciphersuite -> #l:nat -> t:tree cs l -> index_l l -> nat_less (List.Tot.length (tree_resolution t))
let rec resolution_index #cs #l t leaf_index =
  match t with
  | Leaf (Some mi) -> 0
  | Leaf None -> admit() //There should be a precondition that prevent this case
  | Node (Some kp) left right -> (
    match find_index leaf_index kp.unmerged_leafs with
    | Some res ->
      //That is currently not true because a node can contain an unmerged leaf which is actually blanked
      assume (1+res < List.Tot.length (tree_resolution t));
      1+res
    | None -> 0
  )
  | Node None left right ->
    let (child_leaf_index, child_dir) = child_index l leaf_index in
    let (child, _) = order_subtrees child_dir (left, right) in
    let child_resolution_index = resolution_index child child_leaf_index in
    List.Tot.Properties.append_length (tree_resolution left) (tree_resolution right);
    if child_dir = Left then
      child_resolution_index
    else
      (List.Tot.length (tree_resolution left)) +child_resolution_index

val apply_path: #cs:ciphersuite -> #l:nat -> index_l l -> tree cs l -> path cs l -> tree cs l
let rec apply_path #cs #l leaf_index t p =
  match t, p with
  | Leaf _, PLeaf new_mi -> Leaf new_mi
  | Node _ left right, PNode new_kp next_path ->
    let (child_index, child_dir) = child_index l leaf_index in
    if child_dir = Left then
      Node new_kp (apply_path child_index left next_path) right
    else
      Node new_kp left (apply_path child_index right next_path)

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

val node_encap: #cs:ciphersuite -> l:nat -> child_secret:bytes -> ad:bytes -> direction -> pks:list (hpke_public_key cs) -> randomness (hpke_multirecipient_encrypt_entropy_length pks) -> result (key_package cs l & bytes)
let node_encap #cs l child_secret ad dir pks rand =
  node_secret <-- derive_next_path_secret cs child_secret;
  node_keys <-- derive_keypair_from_path_secret cs node_secret;
  ciphertext <-- hpke_multirecipient_encrypt pks bytes_empty ad node_secret rand;
  return (
    {
      kp_public_key = snd node_keys;
      unmerged_leafs = [];
      path_secret_from = dir;
      path_secret_ciphertext = ciphertext;
    },
    node_secret
  )

val node_decap: #cs:ciphersuite -> #l:nat -> child_secret:bytes -> ad:bytes -> i:nat -> dir:direction -> kp:key_package cs l{dir <> kp.path_secret_from ==> i < List.Tot.length kp.path_secret_ciphertext} -> result bytes
let node_decap #cs #l child_secret ad i dir kp =
  if dir = kp.path_secret_from then (
    if i <> 0 then
      fail "node_decap"
    else
      derive_next_path_secret cs child_secret
  ) else (
    let ciphertext = List.Tot.index kp.path_secret_ciphertext i in
    child_keys <-- derive_keypair_from_path_secret cs child_secret;
    let child_sk = fst child_keys in
    hpke_decrypt cs ciphertext.kem_output child_sk bytes_empty ad ciphertext.ciphertext
  )

val update_path_entropy_length: #cs:ciphersuite -> #l:nat -> tree cs l -> index_l l -> nat
let rec update_path_entropy_length #cs #l t leaf_index =
  match t with
  | Leaf _ -> 0
  | Node _ left right ->
    let (new_leaf_index, dir) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    hpke_multirecipient_encrypt_entropy_length (tree_resolution sibling) + update_path_entropy_length child new_leaf_index

val update_path: #cs:ciphersuite -> #l:nat -> t:tree cs l -> leaf_index:index_l l -> leaf_secret:bytes -> ad:bytes -> randomness (update_path_entropy_length t leaf_index) -> Pure (result (path cs l & bytes))
  (requires Seq.length leaf_secret >= hpke_private_key_length cs)
  (ensures fun res -> match res with
    | Error _ -> True
    | Success (_, node_secret) -> Seq.length leaf_secret >= hpke_private_key_length cs
  )
let rec update_path #cs #l t leaf_index leaf_secret ad rand =
  match t with
  | Leaf None -> admit() //TODO: in the previous code, it fails in this case
  | Leaf _ ->
    //TODO: in the previous code, it does some credential check here
    leaf_keys <-- derive_keypair_from_path_secret cs leaf_secret;
    return (PLeaf (Some ({mi_public_key=snd leaf_keys})), leaf_secret)
  | Node _ left right ->
    let (next_leaf_index, dir) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    let (rand_next, rand_cur) = split_randomness rand (hpke_multirecipient_encrypt_entropy_length (tree_resolution sibling)) in
    recursive_call <-- update_path child next_leaf_index leaf_secret ad rand_next;
    let (child_path, child_path_secret) = recursive_call in
    node_encap_call <-- node_encap l child_path_secret ad dir (tree_resolution sibling) rand_cur;
    let (node_kp, node_path_secret) = node_encap_call in
    return (PNode (Some node_kp) child_path, node_path_secret)

val root_secret: #cs:ciphersuite -> #l:nat -> t:tree cs l -> index_l l -> leaf_secret:bytes -> ad:bytes -> result (bytes)
let rec root_secret #cs #l t leaf_index leaf_secret ad =
  match t with
  | Leaf None -> fail ""
  | Leaf (Some _) -> return leaf_secret
  | Node (Some kp) left right -> begin
    if List.Tot.mem leaf_index kp.unmerged_leafs then (
      return leaf_secret
    ) else (
      let (next_leaf_index, dir) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      child_path_secret <-- root_secret child next_leaf_index leaf_secret ad;
      //The condition is here becaus the `i` argument has not sense when dir = kp.path_secret_from.
      //Maybe we should refactor `node_decap`?
      let i = if dir = kp.path_secret_from then 0 else resolution_index child next_leaf_index in
      assume (List.Tot.length (tree_resolution child) == List.Tot.length kp.path_secret_ciphertext);
      node_decap child_path_secret ad i dir kp
    )
  end
  | Node None left right -> begin
    let (next_leaf_index, dir) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    root_secret child next_leaf_index leaf_secret ad
  end
