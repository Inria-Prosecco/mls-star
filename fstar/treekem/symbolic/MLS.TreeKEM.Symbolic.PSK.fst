module MLS.TreeKEM.Symbolic.PSK

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.Crypto
open MLS.Crypto.Derived.Symbolic.ExpandWithLabel
open MLS.TreeKEM.PSK
open MLS.TreeKEM.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let expand_usage_extractedkey_derivedpsk = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.DerivedPSK" empty)

val has_mls_psk_invariants: {|crypto_usages|} -> prop
let has_mls_psk_invariants #cusgs =
  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "derived psk", expand_usage_extractedkey_derivedpsk)

val compute_psk_secret_step_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  label:psk_label_nt bytes -> psk:bytes -> prev_psk_secret:bytes ->
  Lemma
  (requires
    is_well_formed _ (bytes_invariant tr) label /\
    bytes_invariant tr psk /\
    bytes_invariant tr prev_psk_secret /\
    has_mls_psk_invariants
  )
  (ensures (
    match compute_psk_secret_step label psk prev_psk_secret with
    | Success res -> (
      bytes_invariant tr res /\
      get_label tr res `equivalent tr` meet (get_label tr prev_psk_secret) (get_label tr psk)
    )
    | _ -> True
  ))
let compute_psk_secret_step_proof #cinvs tr label psk prev_psk_secret =
  match compute_psk_secret_step label psk prev_psk_secret with
  | Success res -> (
    let Success psk_extracted = kdf_extract (zero_vector #bytes) psk in
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_derivedpsk psk_extracted (KdfExpandKey "KDF.ExtractedKey" (literal_to_bytes Seq.empty)) "derived psk" (serialize (psk_label_nt bytes) label) (kdf_length #bytes);
    let Success psk_input = expand_with_label #bytes psk_extracted "derived psk" (serialize (psk_label_nt bytes) label) (kdf_length #bytes) in
    let Success new_psk_secret = kdf_extract psk_input prev_psk_secret in
    ()
  )
  | _ -> ()

#push-options "--ifuel 1 --fuel 1"
val take:
  #a:Type ->
  l:list a -> i:nat{i <= List.Tot.length l} ->
  list a
let rec take #a l i =
  if i = 0 then
    []
  else
    let h::t = l in
    h::(take t (i-1))
#pop-options

#push-options "--ifuel 1 --fuel 1"
val take_length_eq:
  #a:Type ->
  l:list a ->
  Lemma (take l (List.Tot.length l) == l)
let rec take_length_eq #a l =
  match l with
  | [] -> ()
  | h::t -> take_length_eq t
#pop-options

val psks_bytes_invariant:
  {|crypto_invariants|} ->
  trace ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  prop
let psks_bytes_invariant #cinvs tr l =
  for_allP (is_well_formed_prefix (ps_pre_shared_key_id_nt) (is_publishable tr)) (List.Tot.map fst l) /\
  for_allP (bytes_invariant tr) (List.Tot.map snd l)

val psks_bytes_invariant_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    psks_bytes_invariant tr1 psks /\
    tr1 <$ tr2
  )
  (ensures psks_bytes_invariant tr2 psks)
  [SMTPat (psks_bytes_invariant tr1 psks); SMTPat (tr1 <$ tr2)]
let psks_bytes_invariant_later #cinvs tr1 tr2 psks =
  for_allP_eq (is_well_formed_prefix (ps_pre_shared_key_id_nt) (is_publishable tr1)) (List.Tot.map fst psks);
  for_allP_eq (is_well_formed_prefix (ps_pre_shared_key_id_nt) (is_publishable tr2)) (List.Tot.map fst psks);
  for_allP_eq (is_well_formed (pre_shared_key_id_nt bytes) (is_publishable tr1)) (List.Tot.map fst psks);
  for_allP_eq (is_well_formed (pre_shared_key_id_nt bytes) (is_publishable tr2)) (List.Tot.map fst psks);
  for_allP_eq (bytes_invariant tr1) (List.Tot.map snd psks);
  for_allP_eq (bytes_invariant tr2) (List.Tot.map snd psks)

val psks_label:
  {|crypto_usages|} ->
  trace ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  label
let psks_label #cusgs tr l =
  List.Tot.fold_right meet (List.Tot.map (get_label tr) (List.Tot.map snd l)) public

#push-options "--fuel 1 --ifuel 1"
val psks_label_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    psks_bytes_invariant tr1 psks /\
    tr1 <$ tr2
  )
  (ensures psks_label tr1 psks == psks_label tr2 psks)
  [SMTPat (psks_label tr1 psks); SMTPat (tr1 <$ tr2)]
let rec psks_label_later #cinvs tr1 tr2 psks =
  match psks with
  | [] -> ()
  | h::t ->
    psks_label_later tr1 tr2 t
#pop-options

// lemmas with smt patterns for the [] case to keep ifuel low
#push-options "--fuel 1 --ifuel 1"
val psks_bytes_invariant_nil:
  {|crypto_invariants|} ->
  tr:trace ->
  Lemma (psks_bytes_invariant tr [])
  [SMTPat (psks_bytes_invariant tr [])]
let psks_bytes_invariant_nil #cinvs tr = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val psks_label_nil:
  {|crypto_usages|} ->
  tr:trace ->
  Lemma (psks_label tr [] == public)
  [SMTPat (psks_label tr [])]
let psks_label_nil #cusgs tr = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val psks_bytes_invariant_index:
  {|crypto_invariants|} ->
  tr:trace ->
  l:list (pre_shared_key_id_nt bytes & bytes) -> i:nat{i < List.Tot.length l} ->
  Lemma
  (requires
    psks_bytes_invariant tr l
  )
  (ensures (
    let (id, psk) = List.Tot.index l i in
    is_well_formed (pre_shared_key_id_nt bytes) (bytes_invariant tr) id /\
    bytes_invariant tr psk
  ))
let rec psks_bytes_invariant_index #cinvs tr l i =
  if i = 0 then ()
  else (
    let h::t = l in
    psks_bytes_invariant_index tr t (i-1)
  )
#pop-options

#push-options "--fuel 2 --ifuel 2"
val psks_label_take_lemma:
  {|crypto_usages|} ->
  tr:trace ->
  l:list (pre_shared_key_id_nt bytes & bytes) -> i:nat{i < List.Tot.length l} ->
  Lemma
  (psks_label tr (take l i) `meet` (get_label tr (snd (List.Tot.index l i))) == psks_label tr (take l (i+1)))
let rec psks_label_take_lemma #cusgs tr l i =
  if i = 0 then ()
  else (
    let (id, psk)::t = l in
    psks_label_take_lemma tr t (i-1);
    meet_associative (get_label tr psk) (psks_label tr (take t (i-1))) (get_label tr (snd (List.Tot.index l i)))
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val compute_psk_secret_aux_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  l:list (pre_shared_key_id_nt bytes & bytes) -> ind:nat{ind <= List.Tot.length l} -> psk_secret_ind:bytes ->
  Lemma
  (requires
    psks_bytes_invariant tr l /\
    bytes_invariant tr psk_secret_ind /\
    get_label tr psk_secret_ind `equivalent tr` (psks_label tr (take l ind)) /\
    has_mls_psk_invariants
  )
  (ensures (
    match compute_psk_secret_aux l ind psk_secret_ind with
    | Success res -> (
      bytes_invariant tr res /\
      get_label tr res `equivalent tr` psks_label tr l
    )
    | _ -> True
  ))
  (decreases (List.Tot.length l - ind))
let rec compute_psk_secret_aux_proof #cinvs tr l ind psk_secret_ind =
  match compute_psk_secret_aux l ind psk_secret_ind with
  | Success res -> (
    if ind = List.Tot.length l then (
      take_length_eq l
    ) else (
      let (id, psk) = List.Tot.index l ind in
      psks_bytes_invariant_index tr l ind;
      let label = ({
        id;
        index = ind;
        count = List.Tot.length l;
      }) in
      compute_psk_secret_step_proof tr label psk psk_secret_ind;
      let Success next_psk_secret = compute_psk_secret_step label psk psk_secret_ind in
      psks_label_take_lemma tr l ind;
      compute_psk_secret_aux_proof tr l (ind+1) next_psk_secret
    )
  )
  | _ -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val compute_psk_secret_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  l:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    psks_bytes_invariant tr l /\
    has_mls_psk_invariants
  )
  (ensures (
    match compute_psk_secret l with
    | Success res -> (
      bytes_invariant tr res /\
      get_label tr res `equivalent tr` psks_label tr l
    )
    | _ -> True
  ))
let compute_psk_secret_proof #cinvs tr l =
  compute_psk_secret_aux_proof tr l 0 (zero_vector #bytes)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val drop:
  #a:Type ->
  l:list a -> i:nat{i <= List.Tot.length l} ->
  list a
let rec drop #a l i =
  if i = 0 then
    l
  else
    let h::t = l in
    drop t (i-1)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val drop_everything:
  #a:Type ->
  l:list a ->
  Lemma (drop l (List.Tot.length l) == [])
let rec drop_everything #a l =
  match l with
  | [] -> ()
  | h::t -> drop_everything t
#pop-options

#push-options "--ifuel 1 --fuel 2"
val drop_ind:
  #a:Type ->
  l:list a -> ind:nat{ind < List.Tot.length l} ->
  Lemma ((List.Tot.index l ind)::(drop l (ind+1)) == drop l ind)
let rec drop_ind #a l ind =
  if ind = 0 then ()
  else (
    let h::t = l in
    drop_ind t (ind-1)
  )
#pop-options

val compute_psk_secret_step_inj:
  label1:psk_label_nt bytes -> psk1:bytes -> prev_psk_secret1:bytes ->
  label2:psk_label_nt bytes -> psk2:bytes -> prev_psk_secret2:bytes ->
  Lemma (
    match compute_psk_secret_step label1 psk1 prev_psk_secret1, compute_psk_secret_step label2 psk2 prev_psk_secret2 with
    | Success new_psk_secret1, Success new_psk_secret2 -> (
      new_psk_secret1 == new_psk_secret2 ==> (
        label1 == label2 /\
        psk1 == psk2 /\
        prev_psk_secret1 == prev_psk_secret2
      )
    )
    | _, _ -> True
  )
let compute_psk_secret_step_inj label1 psk1 prev_psk_secret1 label2 psk2 prev_psk_secret2 =
  match compute_psk_secret_step label1 psk1 prev_psk_secret1, compute_psk_secret_step label2 psk2 prev_psk_secret2 with
  | Success new_psk_secret1, Success new_psk_secret2 -> (
    if new_psk_secret1 <> new_psk_secret2 then ()
    else (
      // Not sure why F* needs the following
      let kdf_label1: kdf_label_nt bytes = {
        length = (kdf_length #bytes);
        label = get_mls_label "derived psk";
        context = (serialize #bytes (psk_label_nt bytes) label1);
      } in
      normalize_term_spec (DY.Core.kdf_extract);
      normalize_term_spec (DY.Core.kdf_expand)
    )
  )
  | _, _ -> ()

val compute_psk_secret_step_cannot_be_zero_vector:
  label:psk_label_nt bytes -> psk:bytes -> prev_psk_secret:bytes ->
  Lemma
  (requires
    compute_psk_secret_step label psk prev_psk_secret == Success (zero_vector #bytes)
  )
  (ensures False)
let compute_psk_secret_step_cannot_be_zero_vector label psk prev_psk_secret =
  normalize_term_spec (DY.Core.kdf_extract);
  normalize_term_spec (zero_vector #bytes)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
val compute_psk_secret_aux_inj:
  l1:list (pre_shared_key_id_nt bytes & bytes) -> ind1:nat{ind1 <= List.Tot.length l1} -> psk_secret_ind1:bytes ->
  l2:list (pre_shared_key_id_nt bytes & bytes) -> ind2:nat{ind2 <= List.Tot.length l2} -> psk_secret_ind2:bytes ->
  Lemma
  (requires (
    ((List.Tot.length l1 - ind1) < (List.Tot.length l2 - ind2) ==> ind1 == 0) /\
    ((List.Tot.length l1 - ind1) > (List.Tot.length l2 - ind2) ==> ind2 == 0) /\
    (ind1 == 0 ==> (psk_secret_ind1 == zero_vector #bytes)) /\
    (ind2 == 0 ==> (psk_secret_ind2 == zero_vector #bytes))
  ))
  (ensures (
    match compute_psk_secret_aux l1 ind1 psk_secret_ind1, compute_psk_secret_aux l2 ind2 psk_secret_ind2 with
    | Success res1, Success res2 -> (
      res1 == res2 ==> (
        drop l1 ind1 == drop l2 ind2 /\
        ((ind1 <> List.Tot.length l1 \/ ind2 <> List.Tot.length l2) ==> ind1 == ind2) /\
        psk_secret_ind1 == psk_secret_ind2
      )
    )
    | _ -> True
  ))
  (decreases ((List.Tot.length l1 - ind1) + (List.Tot.length l2 - ind2)))
let rec compute_psk_secret_aux_inj l1 ind1 psk_secret_ind1 l2 ind2 psk_secret_ind2 =
  match compute_psk_secret_aux l1 ind1 psk_secret_ind1, compute_psk_secret_aux l2 ind2 psk_secret_ind2 with
  | Success res1, Success res2 -> (
    if res1 <> res2 then ()
    else (
      if (List.Tot.length l1 - ind1) = (List.Tot.length l2 - ind2) then (
        if (List.Tot.length l1 - ind1) = 0 then (
          drop_everything l1;
          drop_everything l2
        ) else (
          let (id1, psk1) = List.Tot.index l1 ind1 in
          let label1 = ({
            id = id1;
            index = ind1;
            count = List.Tot.length l1;
          }) in
          let Success next_psk_secret1 = compute_psk_secret_step label1 psk1 psk_secret_ind1 in
          let (id2, psk2) = List.Tot.index l2 ind2 in
          let label2 = ({
            id = id2;
            index = ind2;
            count = List.Tot.length l2;
          }) in
          let Success next_psk_secret2 = compute_psk_secret_step label2 psk2 psk_secret_ind2 in
          compute_psk_secret_aux_inj l1 (ind1+1) next_psk_secret1 l2 (ind2+1) next_psk_secret2;
          assert(drop l1 (ind1+1) == drop l2 (ind2+1));
          compute_psk_secret_step_inj label1 psk1 psk_secret_ind1 label2 psk2 psk_secret_ind2;
          assert(List.Tot.index l1 ind1 == List.Tot.index l2 ind2);
          drop_ind l1 ind1;
          drop_ind l2 ind2
        )
      ) else if (List.Tot.length l1 - ind1) < (List.Tot.length l2 - ind2) then (
        let (id2, psk2) = List.Tot.index l2 ind2 in
        let label2 = ({
          id = id2;
          index = ind2;
          count = List.Tot.length l2;
        }) in
        let Success next_psk_secret2 = compute_psk_secret_step label2 psk2 psk_secret_ind2 in
        compute_psk_secret_aux_inj l1 ind1 psk_secret_ind1 l2 (ind2+1) next_psk_secret2;
        compute_psk_secret_step_cannot_be_zero_vector label2 psk2 psk_secret_ind2
      ) else if (List.Tot.length l1 - ind1) > (List.Tot.length l2 - ind2) then (
        let (id1, psk1) = List.Tot.index l1 ind1 in
        let label1 = ({
          id = id1;
          index = ind1;
          count = List.Tot.length l1;
        }) in
        let Success next_psk_secret1 = compute_psk_secret_step label1 psk1 psk_secret_ind1 in
        compute_psk_secret_aux_inj l1 (ind1+1) next_psk_secret1 l2 ind2 psk_secret_ind2;
        compute_psk_secret_step_cannot_be_zero_vector label1 psk1 psk_secret_ind1
      ) else (
        // impossible
        assert(False)
      )
    )
  )
  | _, _ -> ()
#pop-options

#push-options "--fuel 1"
val compute_psk_secret_inj:
  l1:list (pre_shared_key_id_nt bytes & bytes) -> l2:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma (
    match compute_psk_secret l1, compute_psk_secret l2 with
    | Success res1, Success res2 -> (
      res1 == res2 ==> l1 == l2
    )
    | _, _ -> True
  )
let compute_psk_secret_inj l1 l2 =
  compute_psk_secret_aux_inj l1 0 (zero_vector #bytes) l2 0 (zero_vector #bytes)
#pop-options
