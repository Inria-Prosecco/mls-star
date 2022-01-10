module MLS.TreeDEM.PSK

open MLS.Parser
open MLS.Crypto
//open Lib.IntTypes
open Lib.ByteSequence
module NT = MLS.NetworkTypes
open MLS.Parser
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type psk_type =
  | PSKT_external
  | PSKT_reinit
  | PSKT_branch

type psk_id =
  | PSKI_external: id:bytes -> psk_id
  | PSKI_reinit: group_id:bytes -> epoch:nat -> psk_id
  | PSKI_branch: group_id:bytes -> epoch:nat -> psk_id

type psk_id_nonce = {
  id: psk_id;
  nonce: bytes;
}

#push-options "--ifuel 1"
val psk_type_to_network: psk_type -> NT.psk_type_nt
let psk_type_to_network pt =
  match pt with
  | PSKT_external -> NT.PSKT_external
  | PSKT_reinit -> NT.PSKT_reinit
  | PSKT_branch -> NT.PSKT_branch
#pop-options

val network_to_psk_type: NT.psk_type_nt -> result psk_type
let network_to_psk_type pt =
  match pt with
  | NT.PSKT_external -> return PSKT_external
  | NT.PSKT_reinit -> return PSKT_reinit
  | NT.PSKT_branch -> return PSKT_branch
  | _ -> error "network_to_psk_type: invalid psk type"

#push-options "--ifuel 1"
val psk_id_nonce_to_network: psk_id_nonce -> result NT.pre_shared_key_id_nt
let psk_id_nonce_to_network psk =
  if not (Seq.length psk.nonce < 256) then
    error "psk_to_network: nonce is too long"
  else (
    match psk.id with
    | PSKI_external id -> (
      if not (Seq.length id < 256) then
        error "psk_to_network: id is too long"
      else
        return (NT.PSKI_external id psk.nonce)
    )
    | PSKI_reinit group_id epoch ->
      if not (Seq.length group_id < 256) then
        error "psk_to_network: group_id is too long"
      else if not (epoch < pow2 64) then
        error "psk_to_network: epoch is too big"
      else
        return (NT.PSKI_reinit group_id (Lib.IntTypes.u64 epoch) psk.nonce)
    | PSKI_branch group_id epoch ->
      if not (Seq.length group_id < 256) then
        error "psk_to_network: group_id is too long"
      else if not (epoch < pow2 64) then
        error "psk_to_network: epoch is too big"
      else
        return (NT.PSKI_branch group_id (Lib.IntTypes.u64 epoch) psk.nonce)
  )
#pop-options

val network_to_psk_id_nonce: NT.pre_shared_key_id_nt -> result psk_id_nonce
let network_to_psk_id_nonce psk_id =
  match psk_id with
  | NT.PSKI_external id nonce -> return ({id = PSKI_external id; nonce = nonce})
  | NT.PSKI_reinit group_id epoch nonce -> return ({id = PSKI_reinit group_id (Lib.IntTypes.v epoch); nonce = nonce})
  | NT.PSKI_branch group_id epoch nonce -> return ({id = PSKI_reinit group_id (Lib.IntTypes.v epoch); nonce = nonce})
  | _ -> error "network_to_psk: invalid psk type"


type psk_label = {
  id_nonce: psk_id_nonce;
  index: nat;
  count: nat;
}

val psk_label_to_network: psk_label -> result NT.psk_label_nt
let psk_label_to_network label =
  if not (label.count < pow2 16) then
    error "psk_label_to_network: count is too big"
  else if not (label.index < pow2 16) then
    internal_failure "psk_label_to_network: index is too big"
  else (
    id <-- psk_id_nonce_to_network label.id_nonce;
    return ({
      NT.id = id;
      NT.index = Lib.IntTypes.u16 label.index;
      NT.count = Lib.IntTypes.u16 label.count;
    })
  )

val network_to_psk_label: NT.psk_label_nt -> result psk_label
let network_to_psk_label label =
  id_nonce <-- network_to_psk_id_nonce label.NT.id;
  return ({
    id_nonce = id_nonce;
    index = Lib.IntTypes.v label.NT.index;
    count = Lib.IntTypes.v label.NT.count;
  })

// Compute psk_secret[i+1] given psk[i], psk_label[i] and psk_secret[i]
val compute_psk_secret_step: ciphersuite -> psk_label -> bytes -> bytes -> result bytes
let compute_psk_secret_step cs label psk prev_psk_secret =
    label_network <-- psk_label_to_network label;
    psk_extracted <-- kdf_extract cs (zero_vector cs) psk;
    psk_input <-- expand_with_label cs psk_extracted (string_to_bytes "derived psk") (NT.ps_psk_label.serialize label_network) (kdf_length cs);
    new_psk_secret <-- kdf_extract cs psk_input prev_psk_secret;
    return (new_psk_secret <: bytes)

// Compute psk_secret[n] given psk_secret[ind]
val compute_psk_secret_aux: ciphersuite -> l:list (psk_id_nonce & bytes) -> ind:nat{ind <= List.Tot.length l} -> bytes -> Tot (result bytes) (decreases (List.Tot.length l - ind))
let rec compute_psk_secret_aux cs l ind psk_secret_ind =
  if ind = List.Tot.length l then
    return psk_secret_ind
  else (
    let (id_nonce, psk) = List.Tot.index l ind in
    let label = ({
      id_nonce = id_nonce;
      index = ind;
      count = List.Tot.length l;
    }) in
    next_psk_secret <-- compute_psk_secret_step cs label psk psk_secret_ind;
    compute_psk_secret_aux cs l (ind+1) next_psk_secret
  )

val compute_psk_secret: ciphersuite -> list (psk_id_nonce & bytes) -> result bytes
let compute_psk_secret cs l =
  compute_psk_secret_aux cs l 0 (zero_vector cs)
