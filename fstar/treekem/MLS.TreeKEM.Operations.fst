module MLS.TreeKEM.Operations

open Comparse.Bytes
open MLS.Crypto
open MLS.Utils
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeKEM.Types
open MLS.TreeKEM.NetworkTypes
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

(*** TreeKEM operations ***)

val tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> li:leaf_index l i -> member_info bytes ->
  treekem bytes l i
let rec tree_add #bytes #cb #l #i t li lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TNode opt_content left right -> (
    let new_opt_content = (
      match opt_content with
      | None -> None
      | Some content -> (
          Some ({content with unmerged_leaves = insert_sorted li content.unmerged_leaves})
      )
    ) in
    if is_left_leaf li then (
      TNode new_opt_content (tree_add left li lp) right
    ) else (
      TNode new_opt_content left (tree_add right li lp)
    )
  )

val tree_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treekem bytes l i -> pathkem bytes l i li ->
  treekem bytes l i
let rec tree_apply_path #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf mi -> TLeaf (Some mi)
  | TNode _ left right, PNode onp p_next -> (
    if is_left_leaf li then
      TNode onp (tree_apply_path left p_next) right
    else
      TNode onp left (tree_apply_path right p_next)
  )

(*** TreeKEM path generation ***)

val leaf_public_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> leaf_index l i ->
  option (hpke_public_key bytes)
let leaf_public_key #bytes #cb #l #i t leaf_index =
  match leaf_at t leaf_index with
  | None -> None
  | Some mi -> Some (mi.public_key)

val unmerged_leaves_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> list nat ->
  list (hpke_public_key bytes)
let unmerged_leaves_resolution #bytes #cb #l #i t indexes =
  List.Tot.concatMap (fun (index:nat) ->
    if leaf_index_inside l i index  then
      match leaf_public_key t index with
      | None -> []
      | Some res -> [res]
    else
      []
  ) indexes

val tree_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i ->
  list (hpke_public_key bytes)
let rec tree_resolution #bytes #cb #l #i t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some mi) -> [mi.public_key]
  | TNode (Some kp) left right -> (kp.public_key)::(unmerged_leaves_resolution t kp.unmerged_leaves)
  | TNode None left right -> (tree_resolution left)@(tree_resolution right)

val find_index:
  #a:eqtype ->
  a -> l:list a ->
  option (nat_less (List.Tot.length l))
let rec find_index #a x l =
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

val resolution_index:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> leaf_index l i ->
  nat_less (List.Tot.length (tree_resolution t))
let rec resolution_index #bytes #cb #l t leaf_index =
  match t with
  | TLeaf (Some mi) -> (
    0
  )
  | TLeaf None -> admit() //TODO: There should be a precondition that prevent this case
  | TNode (Some kp) left right -> (
    match find_index leaf_index kp.unmerged_leaves with
    | Some res ->
      //That is currently not provable because a node might contain an unmerged leaf which is actually blanked
      assume (1+res < List.Tot.length (tree_resolution t));
      1+res
    | None -> 0
  )
  | TNode None left right ->
    let (child, _) = get_child_sibling t leaf_index in
    let child_resolution_index = resolution_index child leaf_index in
    List.Tot.Properties.append_length (tree_resolution left) (tree_resolution right);
    if is_left_leaf leaf_index then
      child_resolution_index
    else
      (List.Tot.length (tree_resolution left)) + child_resolution_index

val un_addP:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> (nat -> bool) ->
  treekem bytes l i
let rec un_addP #bytes #cb #l #i t pre =
  match t with
  | TLeaf _ -> if pre i then t else TLeaf None
  | TNode okp left right -> (
    let new_okp =
      match okp with
      | None -> None
      | Some kp -> Some ({ kp with unmerged_leaves = List.Tot.filter pre kp.unmerged_leaves })
    in
    TNode new_okp (un_addP left pre) (un_addP right pre)
  )

val forbidden_pre: list nat -> nat -> bool
let forbidden_pre l i =
  not (List.Tot.mem i l)

val original_tree_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  list nat -> treekem bytes l i ->
  list (hpke_public_key bytes)
let original_tree_resolution #bytes #cb #l #i forbidden_leaves t =
  tree_resolution (un_addP t (forbidden_pre forbidden_leaves))

val original_resolution_index:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  forbidden_leaves:list nat -> t:treekem bytes l i -> leaf_index l i ->
  nat_less (List.Tot.length (original_tree_resolution forbidden_leaves t))
let original_resolution_index #bytes #cb #l forbidden_leaves t leaf_index =
  resolution_index (un_addP t (forbidden_pre forbidden_leaves)) leaf_index

val multi_encrypt_with_label_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (hpke_public_key bytes) ->
  list nat
let rec multi_encrypt_with_label_entropy_lengths #bytes #cb pks =
  match pks with
  | [] -> []
  | h::t -> (hpke_private_key_length #bytes)::(multi_encrypt_with_label_entropy_lengths t)

val multi_encrypt_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pks:list (hpke_public_key bytes) -> label:valid_label -> context:bytes -> plaintext:bytes -> randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  result (list (path_secret_ciphertext bytes))
let rec multi_encrypt_with_label #bytes #cb public_keys label context plaintext rand =
  match public_keys with
  | [] -> return []
  | pk::pks ->
    let (rand_cur, rand_next) = dest_randomness rand in
    let? res_hd = encrypt_with_label pk label context plaintext rand_cur in
    let? res_tl = multi_encrypt_with_label pks label context plaintext rand_next in
    return (({kem_output = fst res_hd; ciphertext = snd res_hd} <: path_secret_ciphertext bytes)::res_tl)

val derive_keypair_from_path_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (hpke_private_key bytes & hpke_public_key bytes)
let derive_keypair_from_path_secret #bytes #cb path_secret =
  let? node_secret = derive_secret path_secret "node" in
  hpke_gen_keypair (node_secret <: bytes)

val derive_next_path_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result bytes
let derive_next_path_secret #bytes #cb path_secret =
  let? res = derive_secret path_secret "path" in
  return (res <: bytes)

val node_encap:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  child_secret:bytes -> hpke_info:bytes -> direction -> pks:list (hpke_public_key bytes) -> randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  result (key_package bytes & bytes)
let node_encap #bytes #cb child_secret hpke_info dir pks rand =
  let? node_secret = derive_next_path_secret child_secret in
  let? node_keys = derive_keypair_from_path_secret node_secret in
  let? ciphertext = multi_encrypt_with_label pks "UpdatePathNode" hpke_info node_secret rand in
  return (
    {
      public_key = snd node_keys;
      last_group_context = hpke_info;
      unmerged_leaves = [];
      path_secret_from = dir;
      path_secret_ciphertext = ciphertext;
    },
    node_secret
  )

val node_decap:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  child_secret:bytes -> i:nat -> dir:direction -> kp:key_package bytes{dir <> kp.path_secret_from ==> i < List.Tot.length kp.path_secret_ciphertext} ->
  result bytes
let node_decap #bytes #cb child_secret i dir kp =
  if dir = kp.path_secret_from then (
    if i <> 0 then
      internal_failure "node_decap"
    else
      derive_next_path_secret child_secret
  ) else (
    let ciphertext = List.Tot.index kp.path_secret_ciphertext i in
    let? child_keys = derive_keypair_from_path_secret child_secret in
    let child_sk = fst child_keys in
    decrypt_with_label child_sk "UpdatePathNode" (kp.last_group_context) ciphertext.kem_output ciphertext.ciphertext
  )

val update_path_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> leaf_index l i ->
  list nat
let rec update_path_entropy_lengths #bytes #cb #l #i t leaf_index =
  match t with
  | TLeaf _ -> []
  | TNode _ left right ->
    let (child, sibling) = get_child_sibling t leaf_index in
    if tree_resolution sibling = [] then
      update_path_entropy_lengths child leaf_index
    else
      multi_encrypt_with_label_entropy_lengths (tree_resolution sibling) @ update_path_entropy_lengths child leaf_index

val update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> leaf_index:leaf_index l i -> leaf_secret:bytes -> ad:bytes -> randomness bytes (update_path_entropy_lengths t leaf_index) ->
  Pure (result (pathkem bytes l i leaf_index & bytes))
  (requires length leaf_secret >= hpke_private_key_length #bytes)
  (ensures fun res -> match res with
    | Success (_, node_secret) -> length leaf_secret >= hpke_private_key_length #bytes
    | _ -> True
  )
let rec update_path #bytes #cb #l #i t leaf_index leaf_secret ad rand =
  match t with
  | TLeaf None -> admit() //TODO: in the previous code, it fails in this case
  | TLeaf (Some mi) ->
    //TODO: in the previous code, it does some credential check here
    let? leaf_keys = derive_keypair_from_path_secret leaf_secret in
    return (PLeaf ({public_key=snd leaf_keys;} <: member_info bytes), leaf_secret)
  | TNode okp left right ->
    let (child, sibling) = get_child_sibling t leaf_index in
    if tree_resolution sibling = [] then (
      let next_rand: randomness bytes (update_path_entropy_lengths #_ #_ #(l-1) child leaf_index) = rand in
      let? recursive_call = update_path child leaf_index leaf_secret ad next_rand in
      let (child_path, child_path_secret) = recursive_call in
      return (PNode None child_path, child_path_secret)
    ) else (
      let (rand_cur, rand_next) = split_randomness rand in
      let? recursive_call = update_path child leaf_index leaf_secret ad rand_next in
      let (child_path, child_path_secret) = recursive_call in
      let dir = (if is_left_leaf leaf_index then Left else Right) in
      let? node_encap_call = node_encap child_path_secret ad dir (tree_resolution sibling) rand_cur in
      let (node_kp, node_path_secret) = node_encap_call in
      return (PNode (Some node_kp) child_path, node_path_secret)
    )

(*** TreeKEM compute root secret ***)

val root_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> leaf_index l i -> leaf_secret:bytes ->
  result bytes
let rec root_secret #bytes #cb #l #i t leaf_index leaf_secret =
  match t with
  | TLeaf None -> internal_failure "root_secret: leaf_index corresponds to an empty leaf"
  | TLeaf (Some _) -> return leaf_secret
  | TNode (Some kp) left right -> begin
    if List.Tot.mem leaf_index kp.unmerged_leaves then (
      return leaf_secret
    ) else (
      let dir = if is_left_leaf leaf_index then Left else Right in
      let (child, _) = get_child_sibling t leaf_index in
      let? child_path_secret = root_secret child leaf_index leaf_secret in
      //The condition is here becaus the `i` argument has not sense when dir = kp.path_secret_from.
      //Maybe we should refactor `node_decap`?
      let i = if dir = kp.path_secret_from then 0 else original_resolution_index kp.unmerged_leaves child leaf_index in
      assume (dir <> kp.path_secret_from ==> List.Tot.length (original_tree_resolution kp.unmerged_leaves child) == List.Tot.length kp.path_secret_ciphertext);
      node_decap child_path_secret i dir kp
    )
  end
  | TNode None left right -> begin
    let (child, _) = get_child_sibling t leaf_index in
    root_secret child leaf_index leaf_secret
  end

(*** TreeKEM initialization ***)

val find_least_common_ancestor:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> my_ind:leaf_index l i -> other_ind:leaf_index l i{my_ind <> other_ind} ->
  (res_l:nat & res_i:tree_index res_l & treekem bytes res_l res_i & squash (leaf_index_inside res_l res_i my_ind))
let rec find_least_common_ancestor #bytes #cb #l #i t my_ind other_ind =
  match t with
  | TNode _ left right ->
      if is_left_leaf my_ind = is_left_leaf other_ind then (
        let (child, sibling) = get_child_sibling t my_ind in
        find_least_common_ancestor child my_ind other_ind
      ) else (
        (|l, i, t, ()|)
      )

val path_secret_at_least_common_ancestor:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> my_ind:leaf_index l i -> other_ind:leaf_index l i{my_ind <> other_ind} -> leaf_secret:bytes ->
  result bytes
let path_secret_at_least_common_ancestor #bytes #cb #l t my_ind other_ind leaf_secret =
  let (|_, _, lca, _|) = find_least_common_ancestor t my_ind other_ind in
  root_secret lca my_ind leaf_secret

val empty_path_secret_ciphertext:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  path_secret_ciphertext bytes
let empty_path_secret_ciphertext #bytes #cb = {
    kem_output = mk_zero_vector (hpke_kem_output_length #bytes);
    ciphertext = empty;
  }

val mk_init_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> update_index:leaf_index l i ->
  result (pathkem bytes l i update_index)
let rec mk_init_path_aux #bytes #cb #l t update_index =
  match t with
  | TLeaf None -> error "mk_init_path_aux: update leaf cannot be blanked"
  | TLeaf (Some mi) -> return (PLeaf mi)
  | TNode okp left right -> begin
    let update_dir = if is_left_leaf update_index then Left else Right in
    let (child, _) = get_child_sibling t update_index in
    let new_okp =
      match okp with
      | Some kp -> Some ({ kp with
          path_secret_from = update_dir;
        })
      | None -> None
    in
    let? next = mk_init_path_aux child update_index in
    return (PNode okp next)
  end

val mk_init_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> my_index:leaf_index l i -> update_index:leaf_index l i{my_index <> update_index} -> path_secret:bytes -> hpke_info:bytes ->
  result (pathkem bytes l i update_index)
let rec mk_init_path #bytes #cb #l t my_index update_index path_secret hpke_info =
  match t with
  | TNode okp left right -> begin
    let update_dir = if is_left_leaf update_index then Left else Right in
    let (child, sibling) = get_child_sibling t update_index in
    if is_left_leaf my_index = is_left_leaf update_index then (
      let new_okp =
        match okp with
        | Some kp -> Some ({ kp with
          path_secret_from = update_dir;
        })
        | None -> None
      in
      let? next = mk_init_path child my_index update_index path_secret hpke_info in
      return (PNode new_okp next)
    ) else (
      if not (Some? okp && (Some?.v okp).unmerged_leaves = []) then
        error "mk_init_path: the lowest common ancestor must be non-blank and have empty unmerged leaves"
      else (
        let kp = Some?.v okp in
        let resol_size = List.Tot.length (original_tree_resolution [] sibling) in
        let resol_index = original_resolution_index [] sibling my_index in
        let fake_randomness = mk_zero_vector (hpke_private_key_length #bytes) in
        let? my_pk = from_option "leaf at my_index is empty!" (leaf_public_key t my_index) in
        let? my_path_secret_ciphertext = encrypt_with_label my_pk "UpdatePathNode" hpke_info path_secret fake_randomness in
        let new_kp = { kp with
          path_secret_from = update_dir;
          last_group_context = hpke_info;
          //TODO: put the {kem_output = ...; ...} in a separate function
          path_secret_ciphertext = Seq.seq_to_list (Seq.upd (Seq.create resol_size (empty_path_secret_ciphertext)) resol_index (({kem_output=fst my_path_secret_ciphertext; ciphertext = snd my_path_secret_ciphertext} <: path_secret_ciphertext bytes)));
        } in
        let? next = mk_init_path_aux child update_index in
        return (PNode (Some new_kp) next)
      )
    )
  end
