module TreeKEM

open Lib.Result
open Crypto
open Lib.ByteSequence
open Lib.IntTypes

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
//let key_index (l:nat) (i:index_l l) (sib:tree l) dir : index_l (l+1) =
//  if dir = Left then i else i + length (pub_keys l sib)
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

//TODO: move the following next functions in Crypto.fst? Or is it too specific to MLS?
val expand_with_label: ciphersuite -> secret:bytes -> label:bytes -> context:bytes -> len:size_nat -> result (lbytes len)
let expand_with_label cs secret label context len =
  let kdf_label = todo_bytes in
  kdf_expand cs secret kdf_label len

val derive_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> result (lbytes (kdf_length cs))
let derive_secret cs secret label =
  expand_with_label cs secret label bytes_empty (kdf_length cs)

val derive_keypair_from_path_secret: cs:ciphersuite -> bytes -> result (hpke_private_key cs & hpke_public_key cs)
let derive_keypair_from_path_secret cs path_secret =
  node_secret <-- derive_secret cs path_secret (string_to_bytes "node");
  hpke_gen_keypair cs node_secret

val derive_next_path_secret: cs:ciphersuite -> bytes -> result bytes
let derive_next_path_secret cs path_secret =
  res <-- derive_secret cs path_secret (string_to_bytes "path");
  return (res <: bytes)

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
    node_path_secret <-- derive_next_path_secret cs child_path_secret;
    node_keys <-- derive_keypair_from_path_secret cs node_path_secret;
    encrypted_path_secret <-- hpke_multirecipient_encrypt (tree_resolution sibling) bytes_empty ad node_path_secret rand_cur;
    return (PNode (Some ({
      kp_public_key = snd node_keys;
      unmerged_leafs = [];
      path_secret_from = dir;
      path_secret_ciphertext = encrypted_path_secret
    })) child_path, (node_path_secret <: bytes))

type nat_less (m:nat) = n:nat{n<m}

let rec find_index (#a:eqtype) (x:a) (l:list a): option (nat_less (List.Tot.length l)) =
  match l with
  | [] -> None
  | h::t ->
    if x=h then (
      Some 0
    ) else (
      match find_index x t with
      | Some res -> Some (res+1)
      | None -> None
    )

val find_unmerged_leaf: #cs:ciphersuite -> #l:nat -> tree cs l -> index_l l -> option nat
let rec find_unmerged_leaf #cs #l t leaf_index =
  match t with
  | Leaf _ -> None
  | Node (Some kp) _ _ -> begin
    match find_index leaf_index kp.unmerged_leafs with
    | Some res -> Some (1+res)
    | None -> None
  end
  | Node None left right ->
    let (next_leaf_index, dir) = child_index l leaf_index in
    let (child, sibling) = order_subtrees dir (left, right) in
    match find_unmerged_leaf child next_leaf_index with
    | Some res -> Some (if dir = Left then res else List.Tot.length (tree_resolution left) + res)
    | None -> None

val root_secret: #cs:ciphersuite -> #l:nat -> t:tree cs l -> index_l l -> bytes -> result (bytes & nat_less (List.Tot.length (tree_resolution t)))
let rec root_secret #cs #l t leaf_index leaf_secret =
  match t with
  | Leaf None -> Error ""
  | Leaf (Some _) -> return (leaf_secret, 0)
  | Node (Some kp) left right -> begin
    let opt_unmerged_index = find_index leaf_index kp.unmerged_leafs in
    match opt_unmerged_index with
    | Some unmerged_index ->
      assume (1+unmerged_index < List.Tot.length (tree_resolution t));
      return (leaf_secret, 1+unmerged_index)
    | None ->
      let (next_leaf_index, dir) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      recursive_call <-- root_secret child next_leaf_index leaf_secret;
      let (child_path_secret, i) = recursive_call in
      if dir = kp.path_secret_from then (
        path_secret <-- derive_next_path_secret cs child_path_secret;
        return (path_secret, (0 <: nat_less (List.Tot.length (tree_resolution t)) ))
      ) else (
        child_keys <-- derive_keypair_from_path_secret cs child_path_secret;
        let (sk, pk) = child_keys in
        if i < List.Tot.length (kp.path_secret_ciphertext) then (
          let path_ciphertext = List.Tot.index (kp.path_secret_ciphertext) i in
          node_secret <-- hpke_decrypt cs (path_ciphertext.kem_output) sk bytes_empty todo_bytes (path_ciphertext.ciphertext);
          return (node_secret, (0 <: nat_less (List.Tot.length (tree_resolution t)) ))
        ) else Error ""
      )
  end
  | Node None left right -> begin
    let opt_unmerged_index = find_unmerged_leaf t leaf_index in
    match opt_unmerged_index with
    | Some unmerged_index ->
      assume (unmerged_index < List.Tot.length (tree_resolution t));
      return (leaf_secret, unmerged_index)
    | None -> begin
      let (next_leaf_index, dir) = child_index l leaf_index in
      let (child, sibling) = order_subtrees dir (left, right) in
      recursive_call <-- root_secret child next_leaf_index leaf_secret;
      let (child_path_secret, i) = recursive_call in
      let new_i:nat = if dir = Left then i else i + List.Tot.length (tree_resolution left) in
      assume (0 <= new_i /\ new_i < List.Tot.length (tree_resolution t));
      return (child_path_secret, (new_i <: nat_less (List.Tot.length (tree_resolution t)) ))
    end
  end
