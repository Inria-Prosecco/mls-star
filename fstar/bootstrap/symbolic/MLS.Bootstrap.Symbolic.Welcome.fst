module MLS.Bootstrap.Symbolic.Welcome

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.Result
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.Bootstrap.Symbolic.KeyPackageRef
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.Bootstrap.KeyPackageRef
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.Symbolic
open MLS.Symbolic.Randomness
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.PSK

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1"
val mls_hpke_welcome_pred: {|crypto_usages|} -> encryptwithlabel_crypto_pred
let mls_hpke_welcome_pred #cusgs = {
  pred = (fun tr usg_data msg context ->
    match parse init_key_usage_t usg_data, parse (group_secrets_nt bytes) msg with
    | _, None -> False
    | None, _ -> False
    | Some data, Some group_secrets -> (
      let psk_ids = (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)).serialize group_secrets.psks in
      bytes_well_formed tr psk_ids /\
      get_label tr psk_ids `can_flow tr` public /\ (
        match group_secrets.path_secret with
        | None -> True
        | Some path_secret -> (
          // See MLS.TreeKEM.Symbolic.Tree.Operations.decoded_path_secret_good
          get_label tr path_secret.path_secret `can_flow tr` node_key_label data.me data.leaf_public_key /\
          (exists data. path_secret.path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))
        )
      )
    )
  );
  pred_later = (fun tr1 tr2 usg_data msg context ->
    parse_wf_lemma (group_secrets_nt bytes) (bytes_well_formed tr1) msg
  );
}
#pop-options

val aead_group_info_pred: {|crypto_usages|} -> aead_crypto_predicate
let aead_group_info_pred #cusgs = {
  pred = (fun tr key_usage key nonce msg ad ->
    match parse (group_info_nt bytes) msg with
    | None -> False
    | Some group_info ->
      get_label tr (serialize _ group_info.tbs.group_context) `can_flow tr` public
  );
  pred_later = (fun tr1 tr2 key_usage key nonce msg ad ->
    parse_wf_lemma (group_info_nt bytes) (bytes_well_formed tr1) msg;
    match parse (group_info_nt bytes) msg with
    | None -> ()
    | Some group_info ->
      serialize_wf_lemma _ (bytes_well_formed tr1) group_info.tbs.group_context
  );
}

val has_bootstrap_crypto_invariants: {|crypto_invariants|} -> prop
let has_bootstrap_crypto_invariants #cinvs =
    has_mls_encryptwithlabel_pred ("MLS.InitHpkeKey", "Welcome", mls_hpke_welcome_pred) /\
    has_aead_predicate ("MLS.Bootstrap.WelcomeKey", aead_group_info_pred) /\
    has_mls_keyschedule_invariants

(*** Decryption ***)

#push-options "--fuel 1 --ifuel 2"
val find_my_encrypted_group_secret_spec:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #a:Type ->
  kp_ref_to_kp_secrets:(bytes -> option a) -> l:list (encrypted_group_secrets_nt bytes) ->
  Lemma (
    match find_my_encrypted_group_secret kp_ref_to_kp_secrets l with
    | None -> True
    | Some (new_member, kp_secrets, encrypted_group_secrets) ->
      kp_ref_to_kp_secrets new_member == Some kp_secrets /\
      List.Tot.memP {new_member; encrypted_group_secrets} l
  )
let rec find_my_encrypted_group_secret_spec #bytes #cb kp_ref_to_kp_secrets l =
  match l with
  | [] -> ()
  | h::t -> (
    match kp_ref_to_kp_secrets h.new_member with
    | Some kp_secrets -> ()
    | None -> find_my_encrypted_group_secret_spec kp_ref_to_kp_secrets t
  )
#pop-options

val psk_ids_good:
  {|crypto_invariants|} ->
  tr:trace -> list (pre_shared_key_id_nt bytes) ->
  prop
let psk_ids_good #cinvs tr psk_ids =
  for_allP (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr)) psk_ids

val psk_ids_good_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> psk_ids:list (pre_shared_key_id_nt bytes) ->
  Lemma
  (requires psk_ids_good tr1 psk_ids /\ tr1 <$ tr2)
  (ensures psk_ids_good tr2 psk_ids)
  [SMTPat (psk_ids_good tr1 psk_ids); SMTPat (tr1 <$ tr2)]
let psk_ids_good_later #cinvs tr1 tr2 psk_ids =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (is_well_formed_prefix_weaken ps_pre_shared_key_id_nt (is_publishable tr1) (is_publishable tr2)));
  for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr1)) psk_ids;
  for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr2)) psk_ids

#push-options "--fuel 0 --ifuel 1 --z3rlimit 25"
val _decrypt_group_secrets_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  me:principal -> my_leaf_pk:bytes ->
  my_hpke_sk:hpke_private_key bytes -> my_hpke_ciphertext:hpke_ciphertext_nt bytes -> ad:bytes ->
  Lemma
  (requires
    bytes_invariant tr my_hpke_sk /\
    my_hpke_sk `has_usage tr` init_key_usage me my_leaf_pk /\
    bytes_invariant tr my_hpke_ciphertext.kem_output /\
    bytes_invariant tr my_hpke_ciphertext.ciphertext /\
    bytes_invariant tr ad /\
    has_bootstrap_crypto_invariants
  )
  (ensures (
    match _decrypt_group_secrets my_hpke_sk my_hpke_ciphertext ad with
    | Success group_secrets -> (
      is_well_formed _ (bytes_invariant tr) group_secrets /\
      psk_ids_good tr group_secrets.psks /\ (
        match group_secrets.path_secret with
        | None -> True
        | Some { path_secret } ->
          MLS.TreeKEM.Symbolic.Tree.Operations.decoded_path_secret_good me my_leaf_pk path_secret tr
      )
    )
    | _ -> True
  ))
let _decrypt_group_secrets_proof tr me my_leaf_pk my_hpke_sk my_hpke_ciphertext ad =
    match _decrypt_group_secrets my_hpke_sk my_hpke_ciphertext ad with
    | Success group_secrets -> (
      let Success kem_output = mk_hpke_kem_output (my_hpke_ciphertext.kem_output <: bytes) "decrypt_welcome" "kem_output" in
      assert(bytes_invariant tr kem_output);
      bytes_invariant_decrypt_with_label mls_hpke_welcome_pred "MLS.InitHpkeKey" (init_key_usage_data me my_leaf_pk) tr my_hpke_sk "Welcome" ad kem_output my_hpke_ciphertext.ciphertext;
      let Success group_secrets_bytes = decrypt_with_label my_hpke_sk "Welcome" ad kem_output my_hpke_ciphertext.ciphertext in
      let Success group_secrets = from_option "decrypt_group_secrets: malformed group secrets" (parse (group_secrets_nt bytes) group_secrets_bytes) in
      FStar.Classical.move_requires (parse_wf_lemma (group_secrets_nt bytes) (is_publishable tr)) group_secrets_bytes;
      parse_wf_lemma (group_secrets_nt bytes) (bytes_invariant tr) group_secrets_bytes;
      let psk_ids = (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)).serialize group_secrets.psks in
      let pf (): squash (psk_ids_good tr group_secrets.psks) = (
        assert(is_well_formed_whole (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)) (bytes_invariant tr) group_secrets.psks);
        introduce is_publishable tr group_secrets_bytes ==> is_publishable tr psk_ids with _. (
          parse_wf_lemma (group_secrets_nt bytes) (is_publishable tr) group_secrets_bytes;
          assert(is_well_formed_whole (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)) (is_publishable tr) group_secrets.psks)
        );
        assert(is_well_formed_whole (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)) (is_publishable tr) group_secrets.psks)
      ) in pf ();
      match group_secrets.path_secret with
      | None -> ()
      | Some { path_secret } -> (
        FStar.Classical.move_requires (has_usage_publishable tr path_secret) (KdfExpandKey "MLS.PathSecret" empty)
      )
    )
    | _ -> ()
#pop-options

val one_kp_secrets_good:
  {|crypto_invariants|} ->
  #a:Type ->
  trace -> principal ->
  (a -> result (hpke_private_key bytes)) -> (a -> key_package_nt bytes tkt) ->
  a ->
  prop
let one_kp_secrets_good #a tr me kp_secrets_to_hpke_sk kp_secrets_to_key_package kp_secrets =
  match kp_secrets_to_hpke_sk kp_secrets with
  | Success hpke_sk ->
    bytes_invariant tr hpke_sk /\
    hpke_sk `has_usage tr` init_key_usage me (kp_secrets_to_key_package kp_secrets).tbs.leaf_node.data.content /\
    MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (kp_secrets_to_key_package kp_secrets).tbs.leaf_node.data.credential == Some me
  | _ -> True

val kp_secrets_good:
  {|crypto_invariants|} ->
  #a:Type ->
  trace -> principal ->
  (a -> result (hpke_private_key bytes)) -> (a -> key_package_nt bytes tkt) ->
  (bytes -> option a) ->
  prop
let kp_secrets_good #a tr me kp_secrets_to_hpke_sk kp_secrets_to_key_package kp_ref_to_kp_secrets =
  forall kp_ref.
    let opt_kp_secrets = kp_ref_to_kp_secrets kp_ref in
    match opt_kp_secrets with
    | None -> True
    | Some kp_secrets -> (
      one_kp_secrets_good tr me kp_secrets_to_hpke_sk kp_secrets_to_key_package kp_secrets
    )

val decrypt_group_secrets_proof:
  {|crypto_invariants|} ->
  #a:Type ->
  tr:trace -> me:principal ->
  welcome:welcome_nt bytes -> kp_ref_to_kp_secrets:(bytes -> option a) -> kp_secrets_to_hpke_sk:(a -> result (hpke_private_key bytes)) -> kp_secrets_to_key_package:(a -> key_package_nt bytes tkt) ->
  Lemma
  (requires
    is_well_formed _ (bytes_invariant tr) welcome /\
    kp_secrets_good tr me kp_secrets_to_hpke_sk kp_secrets_to_key_package kp_ref_to_kp_secrets /\
    has_bootstrap_crypto_invariants
  )
  (ensures (
    match decrypt_group_secrets welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk with
    | Success (group_secrets, (my_kp_ref,  my_kp_secrets)) -> (
      is_well_formed _ (bytes_invariant tr) group_secrets /\
      psk_ids_good tr group_secrets.psks /\
      kp_ref_to_kp_secrets my_kp_ref == Some my_kp_secrets /\ (
        match group_secrets.path_secret with
        | None -> True
        | Some { path_secret } ->
          MLS.TreeKEM.Symbolic.Tree.Operations.decoded_path_secret_good me (kp_secrets_to_key_package my_kp_secrets).tbs.leaf_node.data.content path_secret tr
      )
    )
    | _ -> True
  ))
let decrypt_group_secrets_proof tr me welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk kp_secrets_to_key_package =
  match decrypt_group_secrets welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk with
  | Success _ -> (
    let Success (my_kp_ref, my_kp_secrets, my_hpke_ciphertext) = from_option "decrypt_welcome: can't find my encrypted secret" (find_my_encrypted_group_secret kp_ref_to_kp_secrets welcome.secrets) in
    let Success my_hpke_sk = kp_secrets_to_hpke_sk my_kp_secrets in
    let Success group_secrets = _decrypt_group_secrets my_hpke_sk my_hpke_ciphertext welcome.encrypted_group_info in
    assert(Success (group_secrets, (my_kp_ref, my_kp_secrets)) == decrypt_group_secrets welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk);
    find_my_encrypted_group_secret_spec kp_ref_to_kp_secrets welcome.secrets;
    for_allP_eq (is_well_formed_prefix (ps_encrypted_group_secrets_nt) (bytes_invariant tr)) welcome.secrets;
    assert(is_well_formed_prefix (ps_encrypted_group_secrets_nt) (bytes_invariant tr) {new_member = my_kp_ref; encrypted_group_secrets = my_hpke_ciphertext;});
    assert(bytes_invariant tr my_hpke_sk);
    _decrypt_group_secrets_proof tr me (kp_secrets_to_key_package my_kp_secrets).tbs.leaf_node.data.content my_hpke_sk my_hpke_ciphertext welcome.encrypted_group_info;
    ()
  )
  | _ -> ()

#push-options "--z3rlimit 25"
val decrypt_group_info_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> encrypted_group_info:bytes ->
  Lemma
  (requires
    bytes_invariant tr encrypted_group_info /\
    bytes_invariant tr joiner_secret /\
    psks_bytes_invariant tr psks /\
    has_bootstrap_crypto_invariants
  )
  (ensures (
    match decrypt_group_info joiner_secret psks encrypted_group_info with
    | Success group_info -> (
      is_well_formed _ (bytes_invariant tr) group_info /\
      is_well_formed _ (is_publishable tr ) group_info.tbs.group_context
    )
    | _ -> True
  ))
let decrypt_group_info_proof tr joiner_secret psks encrypted_group_info =
  match decrypt_group_info joiner_secret psks encrypted_group_info with
  | Success group_info -> (
    let Success welcome_secret = secret_joiner_to_welcome #bytes joiner_secret psks in
    let Success welcome_key = welcome_secret_to_key #bytes welcome_secret in
    let Success welcome_nonce = welcome_secret_to_nonce welcome_secret in
    let Success group_info_bytes = aead_decrypt welcome_key welcome_nonce empty encrypted_group_info in
    assert(Success group_info == from_option "decrypt_group_info: malformed group info" (parse (group_info_nt bytes) group_info_bytes));
    secret_joiner_to_welcome_proof tr joiner_secret psks;
    welcome_secret_to_key_proof tr welcome_secret;
    welcome_secret_to_nonce_proof tr welcome_secret;
    assert(bytes_invariant tr welcome_key);
    assert(bytes_invariant tr welcome_nonce);
    assert(bytes_invariant tr empty);
    assert(bytes_invariant tr encrypted_group_info);
    assert(bytes_invariant tr group_info_bytes);
    parse_wf_lemma (group_info_nt bytes) (bytes_invariant tr) group_info_bytes;
    assert(is_well_formed _ (bytes_invariant tr) group_info.tbs.group_context);
    FStar.Classical.move_requires (parse_wf_lemma (group_info_nt bytes) (is_publishable tr)) group_info_bytes
  )
  | _ -> ()
#pop-options

(*** Encryption ***)

#push-options "--z3rlimit 25"
val encrypt_one_group_secrets_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  key_package:key_package_nt bytes tkt -> encrypted_group_info:bytes -> group_secrets:group_secrets_nt bytes -> entropy:lbytes bytes (hpke_private_key_length #bytes) ->
  Lemma
  (requires
    Some? (key_package_to_principal key_package) /\
    is_well_formed _ (is_publishable tr) key_package /\
    is_publishable tr encrypted_group_info /\

    is_knowable_by (key_package_to_init_label key_package) tr group_secrets.joiner_secret /\
    (
      match group_secrets.path_secret with
      | Some path_secret ->
        is_knowable_by (key_package_to_init_label key_package) tr path_secret.path_secret /\
        get_label tr path_secret.path_secret `can_flow tr` node_key_label (Some?.v (key_package_to_principal key_package)) key_package.tbs.leaf_node.data.content /\
        (exists data. path_secret.path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))
      | None -> True
    ) /\
    psk_ids_good tr group_secrets.psks /\

    bytes_invariant tr entropy /\
    get_label tr entropy == key_package_to_init_label key_package /\
    entropy `has_usage tr` entropy_usage_for_init_key (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content) /\

    i_have_verified_key_package tr me key_package /\
    trace_invariant tr /\
    has_bootstrap_crypto_invariants /\
    has_key_package_invariant
  )
  (ensures (
    match encrypt_one_group_secrets key_package encrypted_group_info group_secrets entropy with
    | Success encrypted_group_secrets ->
      is_well_formed_prefix ps_encrypted_group_secrets_nt (is_publishable tr) encrypted_group_secrets
    | _ -> True
  ))
let encrypt_one_group_secrets_proof #invs tr me key_package encrypted_group_info group_secrets entropy =
  match encrypt_one_group_secrets key_package encrypted_group_info group_secrets entropy with
  | Success encrypted_group_secrets -> (
    let Success kp_ref = compute_key_package_ref key_package in
    compute_key_package_ref_is_knowable_by tr public key_package;
    let gs_bytes = serialize #bytes (group_secrets_nt bytes) group_secrets in
    let Success leaf_hpke_pk = mk_hpke_public_key key_package.tbs.init_key "encrypt_one_group_secrets" "leaf_hpke_pk" in
    let Success (kem_output, ciphertext) = encrypt_with_label leaf_hpke_pk "Welcome" encrypted_group_info gs_bytes entropy in

    key_package_to_init_label_lemma tr me key_package;

    for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr)) group_secrets.psks;
    for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_knowable_by (key_package_to_init_label key_package) tr)) group_secrets.psks;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (is_well_formed_prefix_weaken ps_pre_shared_key_id_nt (is_publishable tr) (is_knowable_by (key_package_to_init_label key_package) tr)));
    allow_inversion (option (path_secret_nt bytes));
    assert(is_well_formed_prefix ps_group_secrets_nt (is_knowable_by (key_package_to_init_label key_package) tr) group_secrets);
    serialize_wf_lemma _ (is_knowable_by (key_package_to_init_label key_package) tr) group_secrets;
    assert(is_well_formed_whole (ps_prefix_to_ps_whole (ps_mls_list ps_pre_shared_key_id_nt)) (is_publishable tr) group_secrets.psks);

    bytes_invariant_encrypt_with_label
      mls_hpke_welcome_pred "MLS.InitHpkeKey" (init_key_usage_data (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content))
      tr leaf_hpke_pk "Welcome" encrypted_group_info gs_bytes entropy
    ;
    ()
  )
  | _ -> ()
#pop-options

val one_opt_path_secret_good:
  {|crypto_invariants|} ->
  trace -> (key_package_nt bytes tkt & option bytes) ->
  prop
let one_opt_path_secret_good #cinvs tr (key_package, opt_path_secret) =
  match opt_path_secret with
  | Some path_secret ->
    Some? (key_package_to_principal key_package) /\
    is_knowable_by (key_package_to_init_label key_package) tr path_secret /\
    get_label tr path_secret `can_flow tr` node_key_label (Some?.v (key_package_to_principal key_package)) key_package.tbs.leaf_node.data.content /\
    (exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))
  | None -> True

val all_opt_path_secret_good:
  {|crypto_invariants|} ->
  trace -> list (key_package_nt bytes tkt & option bytes) ->
  prop
let all_opt_path_secret_good #cinvs tr key_packages =
  for_allP (one_opt_path_secret_good tr) key_packages

#push-options "--ifuel 2"
val all_opt_path_secret_good_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> key_packages:list (key_package_nt bytes tkt & option bytes) ->
  Lemma
  (requires
    all_opt_path_secret_good tr1 key_packages /\
    tr1 <$ tr2
  )
  (ensures all_opt_path_secret_good tr2 key_packages)
  [SMTPat (all_opt_path_secret_good tr1 key_packages); SMTPat (tr1 <$ tr2)]
let all_opt_path_secret_good_later #cinvs tr1 tr2 key_packages =
  for_allP_eq (one_opt_path_secret_good tr1) key_packages;
  for_allP_eq (one_opt_path_secret_good tr2) key_packages
#pop-options

#push-options "--fuel 1 --ifuel 1"
val encrypt_group_secrets_entropy_ghost_data:
  key_packages:list (key_package_nt bytes tkt & option bytes) ->
  res:randomness_ghost_data{List.Tot.length res == List.Tot.length (encrypt_welcome_entropy_length key_packages)}
let rec encrypt_group_secrets_entropy_ghost_data l =
  match l with
  | [] -> []
  | (key_package, _)::key_packages -> (
    let cur_ghost_data =
      match key_package_to_principal key_package with
      | Some prin ->
        (entropy_usage_for_init_key prin (key_package.tbs.leaf_node.data.content), key_package_to_init_label key_package)
      | None ->
        (NoUsage, DY.Core.Label.Unknown.unknown_label)
    in
    let next_ghost_data = encrypt_group_secrets_entropy_ghost_data key_packages in
    cur_ghost_data::next_ghost_data
  )
#pop-options

val mk_group_secrets_proof:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes) -> path_secret:option bytes ->
  Lemma (
    match mk_group_secrets joiner_secret psks path_secret with
    | Success group_secrets -> (
      group_secrets.joiner_secret == joiner_secret /\
      group_secrets.psks == psks /\ (
        match group_secrets.path_secret, path_secret with
        | Some path_secret_lhs, Some path_secret_rhs -> (path_secret_lhs <: path_secret_nt bytes).path_secret == path_secret_rhs
        | None, None -> True
        | _, _ -> False
      )
    )
    | _ -> True
  )
let mk_group_secrets_proof #bytes #bl joiner_secret psks path_secret = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val encrypt_group_secrets_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  encrypted_group_info:bytes -> joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes) -> key_packages:list (key_package_nt bytes tkt & option bytes) -> rand:randomness bytes (encrypt_welcome_entropy_length key_packages) ->
  Lemma
  (requires
    is_publishable tr encrypted_group_info /\
    for_allP (is_well_formed _ (is_publishable tr)) (List.Tot.map fst key_packages) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst key_packages) /\
    all_opt_path_secret_good tr key_packages /\
    is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (List.Tot.map fst key_packages)) secret) tr joiner_secret /\
    psk_ids_good tr psks /\

    rand `randomness_has_ghost_data tr` (encrypt_group_secrets_entropy_ghost_data key_packages) /\

    trace_invariant tr /\
    has_bootstrap_crypto_invariants /\
    has_key_package_invariant
  )
  (ensures (
    match encrypt_group_secrets encrypted_group_info joiner_secret psks key_packages rand with
    | Success encrypted_group_secrets -> (
      for_allP (is_well_formed_prefix ps_encrypted_group_secrets_nt (is_publishable tr)) encrypted_group_secrets
    )
    | _ -> True
  ))
let rec encrypt_group_secrets_proof #invs tr me encrypted_group_info joiner_secret psks key_packages rand =
  match key_packages with
  | [] -> ()
  | (kp, path_secret)::tail -> (
    if not (Success? (encrypt_group_secrets encrypted_group_info joiner_secret psks key_packages rand)) then ()
    else (
      let (cur_rand, rand_next) = dest_randomness rand in
      mk_group_secrets_proof joiner_secret psks path_secret;
      let Success group_secrets = mk_group_secrets joiner_secret psks path_secret in
      encrypt_one_group_secrets_proof tr me kp encrypted_group_info group_secrets cur_rand;
      let Success res_head = encrypt_one_group_secrets kp encrypted_group_info group_secrets cur_rand in
      encrypt_group_secrets_proof tr me encrypted_group_info joiner_secret psks tail rand_next;
      let Success res_tail = encrypt_group_secrets encrypted_group_info joiner_secret psks tail rand_next in
      ()
    )
  )
#pop-options

val encrypt_group_info_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> group_info:group_info_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    is_well_formed _ (is_publishable tr) group_info /\
    psks_bytes_invariant tr psks /\
    has_bootstrap_crypto_invariants /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match encrypt_group_info joiner_secret psks group_info with
    | Success encrypted_group_info ->
      is_publishable tr encrypted_group_info
    | _ -> True
  ))
let encrypt_group_info_proof #cinvs tr joiner_secret psks group_info =
  if not (Success? (encrypt_group_info joiner_secret psks group_info)) then ()
  else (
    let Success welcome_secret = secret_joiner_to_welcome #bytes joiner_secret psks in
    let Success welcome_key = welcome_secret_to_key #bytes welcome_secret in
    let Success welcome_nonce = welcome_secret_to_nonce welcome_secret in
    let group_info_bytes = serialize (group_info_nt bytes) group_info in
    let Success encrypted_welcome_group_info = aead_encrypt welcome_key welcome_nonce empty group_info_bytes in

    secret_joiner_to_welcome_proof tr joiner_secret psks;
    welcome_secret_to_key_proof tr welcome_secret;
    welcome_secret_to_nonce_proof tr welcome_secret;
    assert(is_well_formed _ (is_publishable tr) group_info.tbs.group_context);
    assert(aead_group_info_pred.pred tr (AeadKey "MLS.Bootstrap.WelcomeKey" empty) welcome_key welcome_nonce group_info_bytes empty)
  )

val encrypt_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  group_info:group_info_nt bytes -> joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> key_packages:list (key_package_nt bytes tkt & option bytes) -> rand:randomness bytes (encrypt_welcome_entropy_length key_packages) ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    is_well_formed _ (is_publishable tr) group_info /\

    for_allP (is_well_formed _ (is_publishable tr)) (List.Tot.map fst key_packages) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst key_packages) /\
    all_opt_path_secret_good tr key_packages /\
    is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (List.Tot.map fst key_packages)) secret) tr joiner_secret /\

    psks_bytes_invariant tr psks /\

    rand `randomness_has_ghost_data tr` (encrypt_group_secrets_entropy_ghost_data key_packages) /\

    trace_invariant tr /\
    has_bootstrap_crypto_invariants /\
    has_mls_keyschedule_invariants /\
    has_key_package_invariant
  )
  (ensures (
    match encrypt_welcome group_info joiner_secret psks key_packages rand with
    | Success welcome -> is_well_formed _ (is_publishable tr) welcome
    | _ -> True
  ))
let encrypt_welcome_proof #cinvs tr me group_info joiner_secret psks key_packages rand =
  if not (Success? (encrypt_welcome group_info joiner_secret psks key_packages rand)) then ()
  else (
    let Success encrypted_group_info = encrypt_group_info joiner_secret psks group_info in
    let Success group_secrets = encrypt_group_secrets encrypted_group_info joiner_secret (List.Tot.map fst psks) key_packages rand in
    encrypt_group_info_proof tr joiner_secret psks group_info;
    encrypt_group_secrets_proof tr me encrypted_group_info joiner_secret (List.Tot.map fst psks) key_packages rand
  )
