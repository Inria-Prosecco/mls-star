module MLS.TreeDEM.PSK

open Comparse
open MLS.Crypto
module NT = MLS.TreeDEM.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type psk_id (bytes:Type0) {|bytes_like bytes|} =
  | PSKI_external: id:bytes -> psk_id bytes
  | PSKI_resumption: usage:NT.resumption_psk_usage_nt -> group_id:bytes -> epoch:nat -> psk_id bytes

type psk_id_nonce (bytes:Type0) {|bytes_like bytes|} = {
  id: psk_id bytes;
  nonce: bytes;
}

#push-options "--ifuel 1"
val psk_id_nonce_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  psk_id_nonce bytes ->
  result (NT.pre_shared_key_id_nt bytes)
let psk_id_nonce_to_network psk =
  if not (length psk.nonce < pow2 30) then
    error "psk_to_network: nonce is too long"
  else (
    match psk.id with
    | PSKI_external id -> (
      if not (length id < pow2 30) then
        error "psk_to_network: id is too long"
      else
        return (NT.PSKI_external id psk.nonce)
    )
    | PSKI_resumption usage group_id epoch ->
      if not (length group_id < pow2 30) then
        error "psk_to_network: group_id is too long"
      else if not (epoch < pow2 64) then
        error "psk_to_network: epoch is too big"
      else
        return (NT.PSKI_resumption usage group_id epoch psk.nonce)
  )
#pop-options

#push-options "--ifuel 1"
val network_to_psk_id_nonce:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  NT.pre_shared_key_id_nt bytes ->
  result (psk_id_nonce bytes)
let network_to_psk_id_nonce psk_id =
  match psk_id with
  | NT.PSKI_external id nonce -> return ({id = PSKI_external id; nonce = nonce})
  | NT.PSKI_resumption usage group_id epoch nonce -> return ({id = PSKI_resumption usage group_id epoch; nonce = nonce})
#pop-options

type psk_label (bytes:Type0) {|bytes_like bytes|} = {
  id_nonce: psk_id_nonce bytes;
  index: nat;
  count: nat;
}

val psk_label_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  psk_label bytes ->
  result (NT.psk_label_nt bytes)
let psk_label_to_network label =
  if not (label.count < pow2 16) then
    error "psk_label_to_network: count is too big"
  else if not (label.index < pow2 16) then
    internal_failure "psk_label_to_network: index is too big"
  else (
    let? id = psk_id_nonce_to_network label.id_nonce in
    return ({
      NT.id = id;
      NT.index = label.index;
      NT.count = label.count;
    })
  )

val network_to_psk_label:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  NT.psk_label_nt bytes ->
  result (psk_label bytes)
let network_to_psk_label label =
  let? id_nonce = network_to_psk_id_nonce label.NT.id in
  return ({
    id_nonce = id_nonce;
    index = label.NT.index;
    count = label.NT.count;
  })

// Compute psk_secret[i+1] given psk[i], psk_label[i] and psk_secret[i]
val compute_psk_secret_step:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  psk_label bytes -> bytes -> bytes ->
  result bytes
let compute_psk_secret_step #bytes #cb label psk prev_psk_secret =
    let? label_network = psk_label_to_network label in
    let? psk_extracted = kdf_extract (zero_vector #bytes) psk in
    let? psk_input = expand_with_label #bytes psk_extracted (string_to_bytes #bytes "derived psk") (serialize (NT.psk_label_nt bytes) label_network) (kdf_length #bytes) in
    let? new_psk_secret = kdf_extract psk_input prev_psk_secret in
    return (new_psk_secret <: bytes)

// Compute psk_secret[n] given psk_secret[ind]
val compute_psk_secret_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:list (psk_id_nonce bytes & bytes) -> ind:nat{ind <= List.Tot.length l} -> bytes ->
  Tot (result bytes)
  (decreases (List.Tot.length l - ind))
let rec compute_psk_secret_aux #bytes #cb l ind psk_secret_ind =
  if ind = List.Tot.length l then
    return psk_secret_ind
  else (
    let (id_nonce, psk) = List.Tot.index l ind in
    let label = ({
      id_nonce = id_nonce;
      index = ind;
      count = List.Tot.length l;
    }) in
    let? next_psk_secret = compute_psk_secret_step label psk psk_secret_ind in
    compute_psk_secret_aux l (ind+1) next_psk_secret
  )

val compute_psk_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (psk_id_nonce bytes & bytes) ->
  result bytes
let compute_psk_secret #bytes #cb l =
  compute_psk_secret_aux l 0 (zero_vector #bytes)
