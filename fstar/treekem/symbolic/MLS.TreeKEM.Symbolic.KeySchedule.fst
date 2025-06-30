module MLS.TreeKEM.Symbolic.KeySchedule

open DY.Core
open DY.Lib
open Comparse
open MLS.Result
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.Symbolic
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.Crypto.Derived.Symbolic.ExpandWithLabel
open MLS.TreeDEM.Message.Transcript
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.PSK
open MLS.TreeKEM.Symbolic.PSK

#set-options "--fuel 0 --ifuel 0"

type commit_is_last_in_tx_hash_aux_witness (bytes:Type0) {|crypto_bytes bytes|} =
  confirmed_transcript_hash_input_nt bytes & lbytes bytes (hash_output_length #bytes)

val commit_is_last_in_tx_hash_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit_nt bytes -> bytes -> commit_is_last_in_tx_hash_aux_witness bytes ->
  prop
let commit_is_last_in_tx_hash_aux #bytes #cb commit confirmed_transcript_hash (tx_hash_input, interim_transcript_hash) =
  Success confirmed_transcript_hash == compute_confirmed_transcript_hash tx_hash_input interim_transcript_hash /\
  tx_hash_input.content.content.content_type == CT_commit /\
  commit == tx_hash_input.content.content.content

val commit_is_last_in_tx_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit_nt bytes -> bytes ->
  prop
let commit_is_last_in_tx_hash #bytes #cb commit confirmed_transcript_hash =
  exists witness. commit_is_last_in_tx_hash_aux commit confirmed_transcript_hash witness

#push-options "--ifuel 1"
val proposal_or_ref_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_ref_nt bytes -> proposal_nt bytes ->
  prop
let proposal_or_ref_rel #bytes #cb por p =
  match por with
  | POR_proposal p' -> p == p'
  | POR_reference ref ->
    Success (ref <: bytes) == make_proposal_ref (serialize _ p)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val proposal_or_refs_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (proposal_or_ref_nt bytes) -> list (proposal_nt bytes) ->
  prop
let rec proposal_or_refs_rel #bytes #cb pors ps =
  match pors, ps with
  | [], [] -> True
  | h1::t1, h2::t2 ->
    proposal_or_ref_rel h1 h2 /\
    proposal_or_refs_rel t1 t2
  | _ -> False
#pop-options

#push-options "--fuel 1 --ifuel 1"
val proposals_to_key_packages:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (proposal_nt bytes) ->
  list (key_package_nt bytes tkt)
let rec proposals_to_key_packages #bytes #bl l =
  match l with
  | [] -> []
  | (P_add {key_package})::t -> key_package::proposals_to_key_packages t
  | _::t -> proposals_to_key_packages t
#pop-options

type tx_hash_contains_joiners_witness (bytes:Type0) {|crypto_bytes bytes|} =
  commit_nt bytes & list (proposal_nt bytes)

val tx_hash_contains_joiners_with_witness:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (key_package_nt bytes tkt) -> tx_hash_contains_joiners_witness bytes ->
  prop
let tx_hash_contains_joiners_with_witness #bytes #cb confirmed_transcript_hash joiners (commit, proposals) =
  commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
  proposal_or_refs_rel commit.proposals proposals /\
  joiners == proposals_to_key_packages proposals

val tx_hash_contains_joiners:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (key_package_nt bytes tkt) ->
  prop
let tx_hash_contains_joiners #bytes #cb confirmed_transcript_hash joiners =
  exists witness. tx_hash_contains_joiners_with_witness confirmed_transcript_hash joiners witness

val intro_tx_hash_contains_joiners:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  confirmed_transcript_hash:bytes -> joiners:list (key_package_nt bytes tkt) ->
  commit:commit_nt bytes -> proposals:list(proposal_nt bytes) ->
  Lemma
  (requires
    commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
    proposal_or_refs_rel commit.proposals proposals /\
    joiners == proposals_to_key_packages proposals
  )
  (ensures tx_hash_contains_joiners confirmed_transcript_hash joiners)
let intro_tx_hash_contains_joiners #bytes #cb confirmed_transcript_hash joiners commit proposals =
  assert(tx_hash_contains_joiners_with_witness confirmed_transcript_hash joiners (commit, proposals))

val compute_confirmed_transcript_hash_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  tx_hash_input1:confirmed_transcript_hash_input_nt bytes -> interim_transcript_hash1:lbytes bytes (hash_output_length #bytes) ->
  tx_hash_input2:confirmed_transcript_hash_input_nt bytes -> interim_transcript_hash2:lbytes bytes (hash_output_length #bytes) ->
  Pure (bytes & bytes)
  (requires
    Success? (compute_confirmed_transcript_hash tx_hash_input1 interim_transcript_hash1) /\
    Success? (compute_confirmed_transcript_hash tx_hash_input2 interim_transcript_hash2) /\
    compute_confirmed_transcript_hash tx_hash_input1 interim_transcript_hash1 == compute_confirmed_transcript_hash tx_hash_input2 interim_transcript_hash2
  )
  (ensures fun (b1, b2) ->
    (
      tx_hash_input1 == tx_hash_input2 /\
      interim_transcript_hash1 == interim_transcript_hash2
    ) \/
    is_hash_collision b1 b2
  )
let compute_confirmed_transcript_hash_inj #bytes #cb tx_hash_input1 interim_transcript_hash1 tx_hash_input2 interim_transcript_hash2 =
  bytes_hasEq #bytes;
  if tx_hash_input1 = tx_hash_input2 && interim_transcript_hash1 = interim_transcript_hash2 then
    (empty, empty)
  else (
    let hash_input_1 = concat #bytes interim_transcript_hash1 (serialize _ tx_hash_input1) in
    let hash_input_2 = concat #bytes interim_transcript_hash2 (serialize _ tx_hash_input2) in
    split_concat #bytes interim_transcript_hash1 (serialize _ tx_hash_input1);
    split_concat #bytes interim_transcript_hash2 (serialize _ tx_hash_input2);
    parse_serialize_inv_lemma #bytes _ tx_hash_input1;
    parse_serialize_inv_lemma #bytes _ tx_hash_input2;
    (hash_input_1, hash_input_2)
  )

val commit_is_last_in_tx_hash_aux_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit1:commit_nt bytes -> commit2:commit_nt bytes ->
  confirmed_transcript_hash:bytes ->
  witness1:commit_is_last_in_tx_hash_aux_witness bytes -> witness2:commit_is_last_in_tx_hash_aux_witness bytes ->
  Pure (bytes & bytes)
  (requires
    commit_is_last_in_tx_hash_aux commit1 confirmed_transcript_hash witness1 /\
    commit_is_last_in_tx_hash_aux commit2 confirmed_transcript_hash witness2
  )
  (ensures fun (b1, b2) ->
    commit1 == commit2 \/
    is_hash_collision b1 b2
  )
let commit_is_last_in_tx_hash_aux_lemma #bytes #cb commit1 commit2 confirmed_transcript_hash (tx_hash_input1, interim_transcript_hash1) (tx_hash_input2, interim_transcript_hash2) =
  compute_confirmed_transcript_hash_inj tx_hash_input1 interim_transcript_hash1 tx_hash_input2 interim_transcript_hash2

val commit_is_last_in_tx_hash_inj_lemma:
  commit1:commit_nt bytes -> commit2:commit_nt bytes ->
  confirmed_transcript_hash:bytes ->
  Lemma
  (requires
    commit_is_last_in_tx_hash commit1 confirmed_transcript_hash /\
    commit_is_last_in_tx_hash commit2 confirmed_transcript_hash
  )
  (ensures commit1 == commit2)
let commit_is_last_in_tx_hash_inj_lemma commit1 commit2 confirmed_transcript_hash =
  eliminate exists witness1 witness2. commit_is_last_in_tx_hash_aux commit1 confirmed_transcript_hash witness1 /\ commit_is_last_in_tx_hash_aux commit2 confirmed_transcript_hash witness2
  returns commit1 == commit2
  with _. (
    let (b1, b2) = commit_is_last_in_tx_hash_aux_lemma commit1 commit2 confirmed_transcript_hash witness1 witness2 in
    hash_injective b1 b2
  )

#push-options "--ifuel 1"
val proposal_or_ref_rel_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_ref:proposal_or_ref_nt bytes ->
  proposal1:proposal_nt bytes -> proposal2:proposal_nt bytes ->
  Pure (bytes & bytes)
  (requires
    proposal_or_ref_rel proposal_or_ref proposal1 /\
    proposal_or_ref_rel proposal_or_ref proposal2
  )
  (ensures fun (b1, b2) ->
    proposal1 == proposal2 \/
    is_hash_collision b1 b2
  )
let proposal_or_ref_rel_lemma #bytes #cb proposal_or_ref proposal1 proposal2 =
  match proposal_or_ref with
  | POR_proposal _ -> (empty, empty)
  | POR_reference ref ->
    parse_serialize_inv_lemma #bytes _ proposal1;
    parse_serialize_inv_lemma #bytes _ proposal2;
    make_proposal_ref_inj (serialize _ proposal1) (serialize _ proposal2)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val proposal_or_refs_rel_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_refs:list (proposal_or_ref_nt bytes) ->
  proposals1:list (proposal_nt bytes) -> proposals2:list (proposal_nt bytes) ->
  Pure (bytes & bytes)
  (requires
    proposal_or_refs_rel proposal_or_refs proposals1 /\
    proposal_or_refs_rel proposal_or_refs proposals2
  )
  (ensures fun (b1, b2) ->
    proposals1 == proposals2 \/
    is_hash_collision b1 b2
  )
let rec proposal_or_refs_rel_lemma #bytes #cb proposal_or_refs proposals1 proposals2 =
  match proposal_or_refs, proposals1, proposals2 with
  | [], [], [] -> (empty, empty)
  | hpor::tpor, h1::t1, h2::t2 ->
    if h1 = h2 then
      proposal_or_refs_rel_lemma tpor t1 t2
    else
      proposal_or_ref_rel_lemma hpor h1 h2
#pop-options

val confirmed_transcript_hash_to_init_label_aux:
  bytes ->
  commit_nt bytes & list (proposal_nt bytes) ->
  label
let confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash (commit, proposals) =
  meet (
    prop_to_label (
      commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
      proposal_or_refs_rel commit.proposals proposals
    )
  ) (
    List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret
  )


val confirmed_transcript_hash_to_init_label:
  bytes ->
  label
let confirmed_transcript_hash_to_init_label confirmed_transcript_hash =
  big_join (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash)

#push-options "--ifuel 1"
val confirmed_transcript_hash_to_init_label_eq:
  confirmed_transcript_hash:bytes ->
  joiners:list (key_package_nt bytes tkt) ->
  Lemma
  (requires tx_hash_contains_joiners confirmed_transcript_hash joiners)
  (ensures
    confirmed_transcript_hash_to_init_label confirmed_transcript_hash
    ==
    List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret
  )
let confirmed_transcript_hash_to_init_label_eq confirmed_transcript_hash joiners =
  eliminate exists witness. tx_hash_contains_joiners_with_witness confirmed_transcript_hash joiners witness
  returns confirmed_transcript_hash_to_init_label confirmed_transcript_hash == List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret
  with _. (
    let (commit, proposals) = witness in
    intro_label_equal
      (confirmed_transcript_hash_to_init_label confirmed_transcript_hash)
      (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret)
      (fun tr ->
        // ->
        big_join_flow_to_component tr (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit, proposals);
        prop_to_label_true (
          commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
          proposal_or_refs_rel commit.proposals proposals
        );

        // <-
        let init_label = List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret in
        introduce forall commit2 proposals2. init_label `can_flow tr` (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit2, proposals2) with (
          let p = 
            commit_is_last_in_tx_hash commit2 confirmed_transcript_hash /\
            proposal_or_refs_rel commit2.proposals proposals2
          in
          eliminate p \/ ~p
          returns init_label `can_flow tr` (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit2, proposals2)
          with _. (
            commit_is_last_in_tx_hash_inj_lemma commit commit2 confirmed_transcript_hash;
            let (b1, b2) = proposal_or_refs_rel_lemma commit.proposals proposals proposals2 in
            FStar.Classical.move_requires_2 hash_injective b1 b2
          ) and _. (
            prop_to_label_false p
          )
        )
      )
  )
#pop-options

#push-options "--ifuel 1"
val expand_usage_extractedkey_joiner: expandwithlabel_crypto_usage
let expand_usage_extractedkey_joiner = {
  get_usage = (fun prk_usage context length -> KdfExpandKey "MLS.TreeKEM.JoinerSecret" empty);
  get_label = (fun prk_usage prk_label context length ->
    match parse (group_context_nt bytes) context with
    | Some group_context ->
      prk_label `join` confirmed_transcript_hash_to_init_label group_context.confirmed_transcript_hash
    | None -> public
  );
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
#pop-options

let expand_usage_extractedkey_epoch = {
  get_usage = (fun prk_usage context length ->
    KdfExpandKey "MLS.TreeKEM.EpochSecret" context
  );
  get_label = (fun prk_usage prk_label context length -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}

val mk_resumption_psk_label:
  principal -> group_context_nt bytes ->
  label
let mk_resumption_psk_label me group_context =
  psk_label me (PSKID_ResumptionPSK group_context.group_id group_context.epoch)

val mk_epoch_secret_label:
  epoch_secret_type -> group_context_nt bytes ->
  label
let mk_epoch_secret_label ty group_context =
  let base_epoch_secret_label = mk_group_secret_label (mk_principal_epoch_secret_label ty) group_context in
  match ty with
  | ResumptionPSK ->
    base_epoch_secret_label `join`
    mk_group_secret_label mk_resumption_psk_label group_context
  | _ -> base_epoch_secret_label

#push-options "--ifuel 1"
val mk_epoch_expandwithlabel_usage:
  epoch_secret_type ->
  expandwithlabel_crypto_usage
let mk_epoch_expandwithlabel_usage ty = {
  get_usage = (fun prk_usage context length ->
    let KdfExpandKey _ data = prk_usage in
    match parse (group_context_nt bytes) data with
    | Some group_context ->
      mk_epoch_secret_usage ty group_context
    | None -> NoUsage
  );
  get_label = (fun prk_usage prk_label context length ->
    let KdfExpandKey _ data = prk_usage in
    match parse (group_context_nt bytes) data with
    | Some group_context ->
      prk_label `join` mk_epoch_secret_label ty group_context
    | None -> public
  );
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
#pop-options

let expand_usage_extractedkey_welcome = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty)
let expand_usage_welcome_key = mk_secret_expandwithlabel_usage (AeadKey "MLS.Bootstrap.WelcomeKey" empty)
let expand_usage_welcome_nonce = mk_public_expandwithlabel_usage NoUsage

let expand_usage_epoch_senderdata = mk_epoch_expandwithlabel_usage SenderDataSecret
let expand_usage_epoch_encryption = mk_epoch_expandwithlabel_usage EncryptionSecret
let expand_usage_epoch_exporter = mk_epoch_expandwithlabel_usage ExporterSecret
let expand_usage_epoch_external = mk_epoch_expandwithlabel_usage ExternalSecret
let expand_usage_epoch_confirmation = mk_epoch_expandwithlabel_usage ConfirmationKey
let expand_usage_epoch_membership = mk_epoch_expandwithlabel_usage MembershipKey
let expand_usage_epoch_resumption = mk_epoch_expandwithlabel_usage ResumptionPSK
let expand_usage_epoch_authentication = mk_epoch_expandwithlabel_usage EpochAuthenticator
let expand_usage_epoch_init = mk_epoch_expandwithlabel_usage InitSecret
let expand_usage_confirmation_tag: kdf_expand_crypto_usage = {
  get_usage = (fun prk_usage info -> NoUsage);
  get_label = (fun prk_usage prk_label info -> public);
  get_label_lemma = (fun tr prk_usage prk_label info -> ());
}

val confirmation_mac_pred: {|crypto_usages|} -> mac_crypto_predicate
let confirmation_mac_pred #cusgs = {
  pred = (fun tr key_usg key confirmed_transcript_hash ->
    True
  );
  pred_later = (fun tr1 tr2 key_usg key confirmed_transcript_hash -> ());
}

val has_mls_keyschedule_invariants: {|crypto_invariants|} -> prop
let has_mls_keyschedule_invariants #cinvs =
  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "joiner", expand_usage_extractedkey_joiner) /\

  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "welcome", expand_usage_extractedkey_welcome) /\
  has_mls_expandwithlabel_usage ("MLS.Bootstrap.WelcomeSecret", "key", expand_usage_welcome_key) /\
  has_mls_expandwithlabel_usage ("MLS.Bootstrap.WelcomeSecret", "nonce", expand_usage_welcome_nonce) /\

  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "epoch", expand_usage_extractedkey_epoch) /\

  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "sender data", expand_usage_epoch_senderdata) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "encryption", expand_usage_epoch_encryption) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "exporter", expand_usage_epoch_exporter) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "external", expand_usage_epoch_external) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "confirm", expand_usage_epoch_confirmation) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "membership", expand_usage_epoch_membership) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "resumption", expand_usage_epoch_resumption) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "authentication", expand_usage_epoch_authentication) /\
  has_mls_expandwithlabel_usage ("MLS.TreeKEM.EpochSecret", "init", expand_usage_epoch_init) /\

  has_mac_predicate ("MLS.TreeKEM.ConfirmationKey", confirmation_mac_pred) /\

  has_mls_psk_invariants

val secret_init_to_joiner_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  init_secret:bytes -> opt_commit_secret:option bytes -> group_context:group_context_nt bytes ->
  joiners:list (key_package_nt bytes tkt) -> // de-hash of confirmed transcript hash
  Lemma
  (requires
    tx_hash_contains_joiners group_context.confirmed_transcript_hash joiners /\
    bytes_invariant tr init_secret /\
    (
      match opt_commit_secret with
      | None -> True
      | Some commit_secret -> bytes_invariant tr commit_secret
    ) /\
    is_well_formed _ (bytes_invariant tr) group_context /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match secret_init_to_joiner init_secret opt_commit_secret group_context with
    | Success joiner_secret -> (
      bytes_invariant tr joiner_secret /\
      joiner_secret `has_usage tr` KdfExpandKey "MLS.TreeKEM.JoinerSecret" empty /\ (
        match opt_commit_secret with
        | None ->
          get_label tr joiner_secret `equivalent tr` ((get_label tr init_secret) `join` List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret)
        | Some commit_secret ->
          get_label tr joiner_secret `equivalent tr` ((get_label tr init_secret `meet` get_label tr commit_secret) `join` List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret)
      )
    )
    | _ -> True
  ))
let secret_init_to_joiner_proof tr init_secret opt_commit_secret group_context joiners =
  match secret_init_to_joiner init_secret opt_commit_secret group_context with
  | Success joiner_secret -> (
    let commit_secret =
      match opt_commit_secret with
      | Some commit_secret -> commit_secret
      | None -> zero_vector #bytes
    in
    let Success prk = kdf_extract init_secret commit_secret in
    assert(Success joiner_secret == expand_with_label #bytes prk "joiner" (serialize _ group_context) (kdf_length #bytes));
    confirmed_transcript_hash_to_init_label_eq group_context.confirmed_transcript_hash joiners;
    serialize_wf_lemma _ (bytes_invariant tr) group_context;
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_joiner prk (KdfExpandKey "KDF.ExtractedKey" empty) "joiner" (serialize _ group_context) (kdf_length #bytes)
  )
  | _ -> ()

val secret_joiner_to_welcome_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    psks_bytes_invariant tr psks /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match secret_joiner_to_welcome joiner_secret psks with
    | Success welcome_secret -> (
      bytes_invariant tr welcome_secret /\
      welcome_secret `has_usage tr` KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty /\
      get_label tr welcome_secret `equivalent tr` (get_label tr joiner_secret `meet` psks_label tr psks)
    )
    | _ -> True
  ))
let secret_joiner_to_welcome_proof tr joiner_secret psks =
  match secret_joiner_to_welcome joiner_secret psks with
  | Success welcome_secret -> (
    compute_psk_secret_proof tr psks;
    let Success psk_secret = compute_psk_secret psks in
    let Success extracted_key = kdf_extract joiner_secret psk_secret in
    assert(Success welcome_secret == expand_with_label #bytes extracted_key "welcome" empty (kdf_length #bytes));
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_welcome extracted_key (KdfExpandKey "KDF.ExtractedKey" empty) "welcome" empty (kdf_length #bytes)
  )
  | _ -> ()

val welcome_secret_to_key_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  welcome_secret:bytes ->
  Lemma
  (requires
    bytes_invariant tr welcome_secret /\
    welcome_secret `has_usage tr` KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match welcome_secret_to_key welcome_secret with
    | Success welcome_key -> (
      bytes_invariant tr welcome_key /\
      welcome_key `has_usage tr` AeadKey "MLS.Bootstrap.WelcomeKey" empty /\
      get_label tr welcome_key `equivalent tr` get_label tr welcome_secret
    )
    | _ -> True
  ))
let welcome_secret_to_key_proof #cinvs tr welcome_secret =
  match welcome_secret_to_key welcome_secret with
  | Success welcome_key -> (
    assert(Success welcome_key == expand_with_label welcome_secret "key" (empty #bytes) (aead_key_length #bytes));
    expand_with_label_lemma tr "MLS.Bootstrap.WelcomeSecret" expand_usage_welcome_key welcome_secret (KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty) "key" empty (aead_key_length #bytes)
  )
  | _ -> ()

val welcome_secret_to_nonce_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  welcome_secret:bytes ->
  Lemma
  (requires
    bytes_invariant tr welcome_secret /\
    welcome_secret `has_usage tr` KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match welcome_secret_to_nonce welcome_secret with
    | Success welcome_nonce -> (
      is_publishable tr welcome_nonce
    )
    | _ -> True
  ))
let welcome_secret_to_nonce_proof tr welcome_secret =
  match welcome_secret_to_nonce welcome_secret with
  | Success welcome_nonce -> (
    assert(Success welcome_nonce == expand_with_label welcome_secret "nonce" (empty #bytes) (aead_nonce_length #bytes));
    expand_with_label_lemma tr "MLS.Bootstrap.WelcomeSecret" expand_usage_welcome_nonce welcome_secret (KdfExpandKey "MLS.Bootstrap.WelcomeSecret" empty) "nonce" empty (aead_nonce_length #bytes)
  )
  | _ -> ()

val secret_joiner_to_epoch_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    psks_bytes_invariant tr psks /\
    is_well_formed _ (bytes_invariant tr) group_context /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match secret_joiner_to_epoch joiner_secret psks group_context with
    | Success epoch_secret -> (
      bytes_invariant tr epoch_secret /\
      epoch_secret `has_usage tr` KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context) /\
      get_label tr epoch_secret `equivalent tr` (get_label tr joiner_secret `meet` psks_label tr psks)
    )
    | _ -> True
  ))
let secret_joiner_to_epoch_proof tr joiner_secret psks group_context =
  match secret_joiner_to_epoch joiner_secret psks group_context with
  | Success epoch_secret -> (
    compute_psk_secret_proof tr psks;
    let Success psk_secret = compute_psk_secret psks in
    let Success extracted_key = kdf_extract joiner_secret psk_secret in
    assert(Success epoch_secret == expand_with_label #bytes extracted_key "epoch" (serialize _ group_context) (kdf_length #bytes));
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_epoch extracted_key (KdfExpandKey "KDF.ExtractedKey" empty) "epoch" (serialize _ group_context) (kdf_length #bytes)
  )
  | _ -> ()

// The proof is the same for all these functions,
// this helper allows to factorize the proof.
#push-options "--ifuel 1"
val secret_epoch_to_X:
  epoch_secret_type -> (
    #bytes:Type0 -> {|crypto_bytes bytes|} ->
    bytes ->
    result (lbytes bytes (kdf_length #bytes))
  )
let secret_epoch_to_X ty =
  match ty with
  | InitSecret -> secret_epoch_to_init
  | SenderDataSecret -> secret_epoch_to_sender_data
  | EncryptionSecret -> secret_epoch_to_encryption
  | ExporterSecret -> secret_epoch_to_exporter
  | ExternalSecret -> secret_epoch_to_external
  | ConfirmationKey -> secret_epoch_to_confirmation
  | MembershipKey -> secret_epoch_to_membership
  | ResumptionPSK -> secret_epoch_to_resumption
  | EpochAuthenticator -> secret_epoch_to_authentication
#pop-options

#push-options "--ifuel 1"
val secret_epoch_to_X_string:
  epoch_secret_type ->
  valid_label
let secret_epoch_to_X_string ty =
  match ty with
  | InitSecret -> "init"
  | SenderDataSecret -> "sender data"
  | EncryptionSecret -> "encryption"
  | ExporterSecret -> "exporter"
  | ExternalSecret -> "external"
  | ConfirmationKey -> "confirm"
  | MembershipKey -> "membership"
  | ResumptionPSK -> "resumption"
  | EpochAuthenticator -> "authentication"
#pop-options

#push-options "--ifuel 1"
val secret_epoch_to_X_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  ty:epoch_secret_type -> epoch_secret:bytes ->
  group_context:group_context_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr epoch_secret /\
    epoch_secret `has_usage tr` KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context) /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match (secret_epoch_to_X ty) epoch_secret with
    | Success x_secret -> (
      bytes_invariant tr x_secret /\
      x_secret `has_usage tr` (mk_epoch_secret_usage ty group_context) /\
      (get_label tr x_secret) `equivalent tr` join (get_label tr epoch_secret) (mk_epoch_secret_label ty group_context)
    )
    | _ -> True
  ))
let secret_epoch_to_X_proof #cinvs tr ty epoch_secret group_context =
  match (secret_epoch_to_X ty) epoch_secret with
  | Success x_secret -> (
    expand_with_label_lemma tr "MLS.TreeKEM.EpochSecret" (mk_epoch_expandwithlabel_usage ty) epoch_secret (KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context)) (secret_epoch_to_X_string ty) empty (kdf_length #bytes)
  )
  | _ -> ()
#pop-options

val compute_confirmation_tag_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  confirmation_key:bytes -> confirmed_transcript_hash:bytes ->
  Lemma
  (requires
    bytes_invariant tr confirmation_key /\
    is_publishable tr confirmed_transcript_hash /\
    (exists group_context. confirmation_key `has_usage tr` (mk_epoch_secret_usage ConfirmationKey group_context)) /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match compute_confirmation_tag confirmation_key confirmed_transcript_hash with
    | Success confirmation_tag ->
      is_publishable tr confirmation_tag
    | _ -> True
  ))
let compute_confirmation_tag_proof #cinvs tr confirmation_key confirmed_transcript_hash = ()
