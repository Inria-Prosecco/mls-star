open Js_of_ocaml
open JsHelpers
open MLS_API

(* HELPERS *)

(* Effectful monadic operator with extra debugging for MLS_Result. *)
let (let*) r f =
  match r with
  | MLS_Result.Success s ->
      f s
  | InternalError s ->
      print_endline ("InternalError: " ^ s);
      Js.null
  | ProtocolError s ->
      print_endline ("ProtocolError: " ^ s);
      Js.null

let entropy_state: Obj.t = Obj.repr ()

(* Destruct something that is in prob (result ...). *)
let (let$) r f =
  let r, _ = r entropy_state in
  let* r = r in
  f r

let print_and_fail s =
  (* Makes sure something shows up in the JS console *)
  print_endline ("ERROR: " ^ s);
  assert false

(* GLOBAL STATE: entroy, bytes instance, etc. *)

let entropy: (MLS_Crypto_Builtins.hacl_star_bytes, Obj.t) MLS_API.entropy ref =
  ref { extract_entropy = fun _ _ -> print_and_fail "Please call setEntropy first" }

let crypto_bytes_ = ref None

let crypto_bytes () =
  match !crypto_bytes_ with
  | Some cb -> cb
  | None -> print_endline ("Must call setCiphersuite first"); assert false

(* Call a function that takes crypto bytes *)
let call_c f =
  f (crypto_bytes ())

(* Call a function that takes crypto bytes followed by entropy *)
let call_ce f =
  f (crypto_bytes ()) () !entropy

(* CONVERSIONS *)

let option_bytes_of_uint8array o =
  Option.map bytes_of_uint8array (Js.Opt.to_option o)

let framing_params_of_js o = {
  encrypt = o##.encrypt;
  padding_size = Z.of_int o##.padding_size_;
  authenticated_data = bytes_of_uint8array o##.authenticated_data_;
}

let leaf_node_params_of_js o =
  { nothing_yet = () }

let commit_params_of_js o =
  let proposals = Array.to_list (Js.to_array o##.proposals) in
  let inline_tree = o##.inline_tree_ in
  let force_update = o##.force_update_ in
  let leaf_node_params = leaf_node_params_of_js o##.leaf_node_params_ in
  { proposals; inline_tree; force_update; leaf_node_params }

let js_of_create_commit_result { commit; welcome; group_info } = object%js
  val commit = uint8array_of_bytes commit
  val welcome = Js.Opt.option (Option.map uint8array_of_bytes welcome)
  val group_info_ = uint8array_of_bytes group_info
end

let js_of_create_key_package_result { key_package; keystore_key; keystore_value } = object%js
  val key_package_ = uint8array_of_bytes key_package
  val keystore_key_ = uint8array_of_bytes keystore_key
  val keystore_value_ = uint8array_of_bytes keystore_value
end

let js_of_processed_message_content = function
  | ApplicationMessage bytes ->
      Obj.magic object%js
        val kind = Js.string "ApplicationMessage"
        val message = uint8array_of_bytes bytes
      end
  | Proposal uv ->
      Obj.magic object%js
        val kind = Js.string "Proposal"
        val unvalidated_proposal_ = uv
      end
  | Commit uc ->
      Obj.magic object%js
        val kind = Js.string "Commit"
        val unvalidated_commit_ = uc
      end

let js_of_processed_message { group_id; epoch; sender; authenticated_data1; content } = object%js
  val group_id_ = uint8array_of_bytes group_id
  val epoch = 0 (* TODO *)
  val sender = sender (* TODO *)
  val authenticated_data_ = uint8array_of_bytes authenticated_data1
  val content = js_of_processed_message_content content
end

let js_of_protocol_version_nt v =
  let open MLS_NetworkTypes in
  match v with
  | PV_mls_reserved -> Js.string "reserved"
  | PV_mls10 -> Js.string "mls10"
  | PV_unknown n -> Js.string ("unknown " ^ string_of_int (Z.to_int n))

let js_of_cipher_suite_nt c =
  let open MLS_NetworkTypes in
  match c with
  | CS_reserved -> Js.string "RESERVED"
  | CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 -> Js.string "MLS_128_DHKEMX25519_AES128GCM_SHA256_ED25519"
  | CS_mls_128_dhkemp256_aes128gcm_sha256_p256 -> Js.string "MLS_128_DHKEMP256_AES128GCM_SHA256_P256"
  | CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> Js.string "MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_ED25519"
  | CS_mls_256_dhkemx448_aes256gcm_sha512_ed448 -> Js.string "MLS_256_DHKEMX448_AES256GCM_SHA512_ED448"
  | CS_mls_256_dhkemp521_aes256gcm_sha512_p521 -> Js.string "MLS_256_DHKEMP521_AES256GCM_SHA512_P521"
  | CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448 -> Js.string "MLS_256_DHKEMX448_CHACHA20POLY1305_SHA512_ED448"
  | CS_mls_256_dhkemp384_aes256gcm_sha384_p384 -> Js.string "MLS_256_DHKEMP384_AES256GCM_SHA384_P384"
  | CS_unknown n -> Js.string ("UNKNOWN " ^ string_of_int (Z.to_int n))

let js_of_hpke_ciphertext_nt c =
  let open MLS_TreeKEM_NetworkTypes in
  object%js
    val kem_output_ = c.kem_output
    val ciphertext = c.ciphertext
  end

let js_of_content_type_nt c =
  let open MLS_TreeDEM_NetworkTypes in
  match c with
  | CT_application -> Js.string "application"
  | CT_proposal -> Js.string "proposal"
  | CT_commit -> Js.string "commit"

let js_of_extension_type_nt ext_type =
  let open MLS_NetworkTypes in
  match ext_type with
  | ET_reserved -> Js.string "reserved"
  | ET_application_id -> Js.string "application_id"
  | ET_ratchet_tree -> Js.string "ratchet_tree"
  | ET_required_capabilities -> Js.string "required_capabilities"
  | ET_external_pub -> Js.string "external_pub"
  | ET_external_senders -> Js.string "external_senders"
  | ET_unknown n -> Js.string ("unknown " ^ (string_of_int (Z.to_int n)))

let js_of_extension_nt ext =
  let open MLS_NetworkTypes in
  object%js
    val extension_type_ = js_of_extension_type_nt ext.extension_type
    val extension_data_ = uint8array_of_bytes ext.extension_data
  end

let js_of_credential_type_nt ct =
  let open MLS_NetworkTypes in
  match ct with
  | CT_reserved -> Js.string "reserved"
  | CT_basic -> Js.string "basic"
  | CT_x509 -> Js.string "x509"
  | CT_unknown n -> Js.string ("reserved " ^ string_of_int (Z.to_int n))

let js_of_credential_nt cred =
  let open MLS_NetworkTypes in
  match cred with
  | C_basic identity ->
    Obj.magic object%js
      val credential_type_ = Js.string "basic"
      val identity = uint8array_of_bytes identity
    end
  | C_x509 chain ->
    Obj.magic object%js
      val credential_type_ = Js.string "x509"
      val certificates = Js.array (Array.of_list (List.map uint8array_of_bytes chain))
    end

let js_of_proposal_type_nt pt =
  let open MLS_NetworkTypes in
  match pt with
  | PT_reserved -> Js.string "reserved"
  | PT_add -> Js.string "add"
  | PT_update -> Js.string "update"
  | PT_remove -> Js.string "remove"
  | PT_psk -> Js.string "psk"
  | PT_reinit -> Js.string "reinit"
  | PT_external_init -> Js.string "external_init"
  | PT_group_context_extensions -> Js.string "group_context_extensions"
  | PT_unknown n -> Js.string ("unknown " ^ string_of_int (Z.to_int n))

let js_of_capabilities_nt capabilities =
  let open MLS_TreeSync_NetworkTypes in
  object%js
    val versions = Js.array (Array.of_list (List.map js_of_protocol_version_nt capabilities.versions))
    val cipher_suites_ = Js.array (Array.of_list (List.map js_of_cipher_suite_nt capabilities.ciphersuites))
    val extensions = Js.array (Array.of_list (List.map js_of_extension_type_nt capabilities.extensions))
    val proposals = Js.array (Array.of_list (List.map js_of_proposal_type_nt capabilities.proposals))
    val credentials = Js.array (Array.of_list (List.map js_of_credential_type_nt capabilities.credentials))
  end

let js_of_lifetime_nt lifetime =
  let open MLS_TreeSync_NetworkTypes in
  object%js
    val not_before_ = lifetime.not_before
    val not_after_ = lifetime.not_after
  end

let js_of_leaf_node_nt ln =
  let open MLS_TreeSync_NetworkTypes in
  (* Big copy-paste, can we do better? *)
  match ln.data.source with
  | LNS_key_package ->
    Obj.magic object%js
      val encryption_key_ = uint8array_of_bytes (Obj.magic ln.data.content)
      val signature_key_ = uint8array_of_bytes ln.data.signature_key
      val credential = js_of_credential_nt ln.data.credential
      val capabilities = js_of_capabilities_nt ln.data.capabilities
      val leaf_node_source_ = Js.string "key_package"
      val lifetime = js_of_lifetime_nt (Obj.magic ln.data.lifetime)
      val extensions = Js.array (Array.of_list (List.map js_of_extension_nt ln.data.extensions1))
      val signature = uint8array_of_bytes ln.signature
    end
  | LNS_update ->
    Obj.magic object%js
      val encryption_key_ = uint8array_of_bytes (Obj.magic ln.data.content)
      val signature_key_ = uint8array_of_bytes ln.data.signature_key
      val credential = js_of_credential_nt ln.data.credential
      val capabilities = js_of_capabilities_nt ln.data.capabilities
      val leaf_node_source_ = Js.string "update"
      val extensions = Js.array (Array.of_list (List.map js_of_extension_nt ln.data.extensions1))
      val signature = uint8array_of_bytes ln.signature
    end
  | LNS_commit ->
    Obj.magic object%js
      val encryption_key_ = uint8array_of_bytes (Obj.magic ln.data.content)
      val signature_key_ = uint8array_of_bytes ln.data.signature_key
      val credential = js_of_credential_nt ln.data.credential
      val capabilities = js_of_capabilities_nt ln.data.capabilities
      val leaf_node_source_ = Js.string "commit"
      val parent_hash_ = uint8array_of_bytes (Obj.magic ln.data.parent_hash)
      val extensions = Js.array (Array.of_list (List.map js_of_extension_nt ln.data.extensions1))
      val signature = uint8array_of_bytes ln.signature
    end

let js_of_key_package_nt kp =
  let open MLS_Bootstrap_NetworkTypes in
  object%js
    val version = js_of_protocol_version_nt kp.tbs.version
    val cipher_suite_ = js_of_cipher_suite_nt kp.tbs.cipher_suite
    val init_key_ = uint8array_of_bytes kp.tbs.init_key
    val leaf_node_ = js_of_leaf_node_nt kp.tbs.leaf_node
    val extensions = Js.array (Array.of_list (List.map js_of_extension_nt kp.tbs.extensions))
    val signature = uint8array_of_bytes kp.signature
  end

let js_of_sender_nt sender =
  let open MLS_TreeDEM_NetworkTypes in
  match sender with
  | S_member leaf_index ->
    Obj.magic object%js
      val sender_type_ = Js.string "member"
      val leaf_index_ = Z.to_int leaf_index
    end
  | S_external sender_index ->
    Obj.magic object%js
      val sender_type_ = Js.string "external"
      val sender_index_ = Z.to_int sender_index
    end
  | S_new_member_proposal ->
    Obj.magic object%js
      val sender_type_ = Js.string "new_member_proposal"
    end
  | S_new_member_commit ->
    Obj.magic object%js
      val sender_type_ = Js.string "new_member_commit"
    end

let js_of_pre_shared_key_id psk_id =
  let open MLS_TreeKEM_NetworkTypes in
  match psk_id with
  | PSKI_external (psk_id, psk_nonce) ->
    Obj.magic object%js
      val psktype = Js.string "external"
      val psk_id_ = uint8array_of_bytes psk_id
      val psk_nonce_ = uint8array_of_bytes psk_nonce
    end
  | PSKI_resumption (usage, psk_group_id, psk_epoch, psk_nonce) ->
    Obj.magic object%js
      val usage =
        match usage with
        | RPSKU_application -> Js.string "application"
        | RPSKU_reinit -> Js.string "reinit"
        | RPSKU_branch -> Js.string "branch"
      val psk_group_id_ = uint8array_of_bytes psk_group_id
      val psk_epoch_ = Z.to_int psk_epoch
      val psk_nonce_ = uint8array_of_bytes psk_nonce
    end

let js_of_proposal_nt proposal =
  let open MLS_TreeDEM_NetworkTypes in
  match proposal with
  | P_add add ->
    Obj.magic object%js
      val proposal_type_ = Js.string "add"
      val key_package_ = js_of_key_package_nt add.key_package
    end
  | P_update update ->
    Obj.magic object%js
      val proposal_type_ = Js.string "update"
      val leaf_node_ = js_of_leaf_node_nt update.leaf_node
    end
  | P_remove remove ->
    Obj.magic object%js
      val proposal_type_ = Js.string "remove"
      val removed = Z.to_int remove.removed
    end
  | P_psk psk ->
    Obj.magic object%js
      val proposal_type_ = Js.string "psk"
      val psk = js_of_pre_shared_key_id psk.psk
    end
  | P_reinit reinit ->
    Obj.magic object%js
      val proposal_type_ = Js.string "reinit"
      val group_id_ = uint8array_of_bytes reinit.group_id
      val version = js_of_protocol_version_nt reinit.version
      val cipher_suite_ = js_of_cipher_suite_nt reinit.cipher_suite
      val extensions = Js.array (Array.of_list (List.map js_of_extension_nt reinit.extensions))
    end
  | P_external_init external_init ->
    Obj.magic object%js
      val proposal_type_ = Js.string "external_init"
      val kem_output_ = uint8array_of_bytes external_init.kem_output
    end
  | P_group_context_extensions group_context_extensions ->
    Obj.magic object%js
      val proposal_type_ = Js.string "group_context_extensions"
      val extensions = Js.array (Array.of_list (List.map js_of_extension_nt group_context_extensions.extensions1))
    end

let js_of_proposal_or_ref_nt por =
  let open MLS_TreeDEM_NetworkTypes in
  match por with
  | POR_proposal proposal ->
    Obj.magic object%js
      val type_ = Js.string "proposal"
      val proposal = js_of_proposal_nt proposal
    end
  | POR_reference ref ->
    Obj.magic object%js
      val type_ = Js.string "reference"
      val reference = uint8array_of_bytes ref
    end

let js_of_update_path_node_nt node =
  let open MLS_TreeKEM_NetworkTypes in
  object%js
    val encryption_key_ = uint8array_of_bytes node.encryption_key
    val encrypted_path_secret_ = Js.array (Array.of_list (List.map js_of_hpke_ciphertext_nt node.encrypted_path_secret))
  end

let js_of_update_path_nt path =
  let open MLS_TreeKEM_NetworkTypes in
  object%js
    val leaf_node_ = js_of_leaf_node_nt path.leaf_node
    val nodes = Js.array (Array.of_list (List.map js_of_update_path_node_nt path.nodes))
  end

let js_of_commit_nt commit =
  let open MLS_TreeDEM_NetworkTypes in
  object%js
    val proposals = Js.array (Array.of_list (List.map js_of_proposal_or_ref_nt commit.proposals))
    val path = Js.Opt.option (Option.map js_of_update_path_nt commit.path)
  end

let js_of_framed_content_nt content =
  let open MLS_TreeDEM_NetworkTypes in
  match content.content1.content_type with
  | CT_application ->
    Obj.magic object%js
      val group_id_ = uint8array_of_bytes content.group_id1
      val epoch = Z.to_int content.epoch
      val sender = js_of_sender_nt content.sender
      val authenticated_data_ = uint8array_of_bytes content.authenticated_data
      val content_type_ = Js.string "application"
      val application_data_ = uint8array_of_bytes (Obj.magic content.content1.content)
    end
  | CT_proposal ->
    Obj.magic object%js
      val group_id_ = uint8array_of_bytes content.group_id1
      val epoch = Z.to_int content.epoch
      val sender = js_of_sender_nt content.sender
      val authenticated_data_ = uint8array_of_bytes content.authenticated_data
      val content_type_ = Js.string "proposal"
      val proposal = js_of_proposal_nt (Obj.magic content.content1.content)
    end
  | CT_commit ->
    Obj.magic object%js
      val group_id_ = uint8array_of_bytes content.group_id1
      val epoch = Z.to_int content.epoch
      val sender = js_of_sender_nt content.sender
      val authenticated_data_ = uint8array_of_bytes content.authenticated_data
      val content_type_ = Js.string "commit"
      val commit = js_of_commit_nt (Obj.magic content.content1.content)
    end

let js_of_framed_content_auth_data_nt auth ct =
  let open MLS_TreeDEM_NetworkTypes in
  match ct with
  | CT_commit ->
    Obj.magic object%js
      val signature = uint8array_of_bytes auth.signature
      val confirmation_tag_ = uint8array_of_bytes (Obj.magic auth.confirmation_tag)
    end
  | _ ->
    Obj.magic object%js
      val signature = uint8array_of_bytes auth.signature
    end

let js_of_public_message_nt msg =
  let open MLS_TreeDEM_NetworkTypes in
  match msg.content4.sender with
  | S_member _ ->
    Obj.magic object%js
      val content = js_of_framed_content_nt msg.content4
      val auth = js_of_framed_content_auth_data_nt msg.auth2 msg.content4.content1.content_type
      val membership_tag_ = uint8array_of_bytes (Obj.magic msg.membership_tag)
    end
  | _ ->
    Obj.magic object%js
      val content = js_of_framed_content_nt msg.content4
      val auth = js_of_framed_content_auth_data_nt msg.auth2
    end

let js_of_private_message_nt msg =
  let open MLS_TreeDEM_NetworkTypes in
  object%js
    val group_id_ = uint8array_of_bytes msg.group_id2
    val epoch = Z.to_int msg.epoch1
    val content_type_ = js_of_content_type_nt msg.content_type1
    val authenticated_data_ = uint8array_of_bytes msg.authenticated_data1
    val encrypted_sender_data_ = uint8array_of_bytes msg.encrypted_sender_data
    val ciphertext = uint8array_of_bytes msg.ciphertext
  end

let js_of_encrypted_group_secrets_nt egs =
  let open MLS_Bootstrap_NetworkTypes in
  object%js
    val new_member_ = uint8array_of_bytes egs.new_member
    val encrypted_group_secrets_ = js_of_hpke_ciphertext_nt egs.encrypted_group_secrets
  end

let js_of_welcome_nt w =
  let open MLS_Bootstrap_NetworkTypes in
  object%js
    val cipher_suite_ = js_of_cipher_suite_nt w.cipher_suite1
    val secrets = Js.array (Array.of_list (List.map js_of_encrypted_group_secrets_nt w.secrets))
    val encrypted_group_info_ = uint8array_of_bytes w.encrypted_group_info
  end

let js_of_group_context_nt gc =
  let open MLS_NetworkTypes in
  object%js
    val version = js_of_protocol_version_nt gc.version
    val cipher_suite_ = js_of_cipher_suite_nt gc.cipher_suite
    val group_id_ = uint8array_of_bytes gc.group_id
    val epoch = gc.epoch
    val tree_hash_ = uint8array_of_bytes gc.tree_hash
    val confirmed_transcript_hash_ = uint8array_of_bytes gc.confirmed_transcript_hash
    val extensions = Js.array (Array.of_list (List.map js_of_extension_nt gc.extensions))
  end

let js_of_group_info_nt gi =
  let open MLS_Bootstrap_NetworkTypes in
  object%js
    val group_context_ = js_of_group_context_nt gi.tbs1.group_context
    val extensions = Js.array (Array.of_list (List.map js_of_extension_nt gi.tbs1.extensions1))
    val confirmation_tag_ = uint8array_of_bytes gi.tbs1.confirmation_tag
    val signer = gi.tbs1.signer
    val signature = uint8array_of_bytes gi.signature1
  end

let js_of_mls_message_nt msg =
  let open MLS_TreeDEM_NetworkTypes in
  match msg with
  | M_mls10 msg10 -> (
    match msg10 with
    | M_public_message pub_msg -> (
      Obj.magic object%js
        val version = Js.string "mls10"
        val wire_format_ = Js.string "mls_public_message"
        val public_message_ = js_of_public_message_nt pub_msg
      end
    )
    | M_private_message priv_msg -> (
      Obj.magic object%js
        val version = Js.string "mls10"
        val wire_format_ = Js.string "mls_private_message"
        val private_message_ = js_of_private_message_nt priv_msg
      end
    )
    | M_welcome welcome -> (
      Obj.magic object%js
        val version = Js.string "mls10"
        val wire_format_ = Js.string "mls_welcome"
        val welcome = js_of_welcome_nt welcome
      end
    )
    | M_group_info group_info -> (
      Obj.magic object%js
        val version = Js.string "mls10"
        val wire_format_ = Js.string "mls_group_info"
        val group_info_ = js_of_group_info_nt group_info
      end
    )
    | M_key_package key_package -> (
      Obj.magic object%js
        val version = Js.string "mls10"
        val wire_format_ = Js.string "mls_key_package"
        val key_package_ = js_of_key_package_nt key_package
      end
    )
  )
  | _ -> Js.null

let _ =
  Js.export_all (object%js

    (* NEW API: global state *)

    method setCrypto (arg: _ Js.t) =
      Js.Unsafe.global##._MyCrypto := arg

    (* Expects a JS function that takes a Number and returns that many random
       bytes as a UInt8Array. *)
    method setEntropy (f: _ Js.t) =
      entropy := { extract_entropy = fun n state ->
        let bytes = bytes_of_uint8array (Js.Unsafe.fun_call f [| Js.Unsafe.inject (Z.to_int n) |]) in
        MLS_Result.Success bytes, state
      }

    (* Expects a JS string that contains the expected ciphersuite *)
    method setCiphersuite (cs: _ Js.t) =
      let cs = Js.to_string cs in
      if !crypto_bytes_ <> None then
        print_and_fail "Cannot dynamically change ciphersuites";
      let ac = match cs with
        | "MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519" ->
            MLS_Crypto_Builtins.AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
        | "MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519" ->
            AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
        | _ ->
            print_and_fail ("Unsupported ciphersuite: " ^ cs)
      in
      crypto_bytes_ := Some MLS_Crypto_Builtins.(mk_concrete_crypto_bytes ac)

    (* NEW API: binders for MLS.API.fst (via MLS_API.ml) *)

    method generateSignatureKeyPair =
      let$ kp = call_ce generate_signature_keypair in
      Js.some kp

    method getSignaturePublicKey kp =
      let pk = call_c get_signature_public_key kp in
      Js.some (uint8array_of_bytes pk)

    method mkBasicCredential kp identity =
      let identity = bytes_of_uint8array identity in
      let* cp = call_c mk_basic_credential kp identity in
      Js.some cp

    method mkX509Credential kp chain =
      let chain = List.map bytes_of_uint8array (Array.to_list (Js.to_array chain)) in
      let* cp = call_c mk_x509_credential kp chain in
      Js.some cp

    method getPublicCredential cp =
      let c = call_c get_public_credential cp in
      Js.some c

    method createKeyPackage cp =
      let$ ckpr = call_ce create_key_package cp in
      Js.some (js_of_create_key_package_result ckpr)

    method createGroup cp =
      let$ g = call_ce create_group cp in
      Js.some g

    method startJoinGroup welcome lookup =
      let welcome = bytes_of_uint8array welcome in
      let* sjgo = call_c start_join_group welcome (fun b ->
        let b = uint8array_of_bytes b in
        option_bytes_of_uint8array (Js.Unsafe.fun_call lookup [| Js.Unsafe.inject b |])
      ) in
      Js.some sjgo

    method continueJoinGroup sjgo ort =
      let ort = option_bytes_of_uint8array ort in
      let* cjgo = call_c continue_join_group sjgo ort in
      Js.some cjgo

    method finalizeJoinGroup sb =
      let* g = call_c finalize_join_group sb in
      Js.some g

    method exportSecret g l ctx len =
      let l = Js.to_string l in
      let ctx = bytes_of_uint8array ctx in
      let len = Z.of_int len in
      let* r = call_c export_secret g l ctx len in
      Js.some (uint8array_of_bytes r)

    method epochAuthenticator g =
      let* r = call_c epoch_authenticator g in
      Js.some (uint8array_of_bytes r)

    method epoch g =
      let r = call_c epoch g in
      Js.some (Z.to_int (FStar_UInt64.v r))

    method groupId g =
      let r = call_c group_id g in
      Js.some (uint8array_of_bytes r)

    method getNewCredentials uv =
      let* r = call_c get_new_credentials uv in
      Js.some (Js.array (Array.of_list r))

    method getNewCredential uv =
      let* r = call_c get_new_credential uv in
      Js.some (Js.Opt.option r)

    method processMessage g bytes =
      let bytes = bytes_of_uint8array bytes in
      let* pm, g = call_c process_message g bytes in
      Js.some (object%js
        val processed_message_ = js_of_processed_message pm
        val group = g
      end)

    method iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheCommit uv =
      Js.some (call_c i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit uv)

    method mergeCommit g vc =
      let* g = call_c merge_commit g vc in
      Js.some g

    method iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheProposal up =
      Js.some (call_c i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal up)

    method queueNewProposal g vp =
      let* g = call_c queue_new_proposal g vp in
      Js.some g

    method sendApplicationMessage g fp m =
      let fp = framing_params_of_js fp in
      let m = bytes_of_uint8array m in
      let$ message, g = call_ce send_application_message g fp m in
      Js.some (object%js
        val message = uint8array_of_bytes message
        val group = g
      end)

    method proposeAddMember g fp kp =
      let fp = framing_params_of_js fp in
      let kp = bytes_of_uint8array kp in
      let$ message, g = call_ce propose_add_member g fp kp in
      Js.some (object%js
        val message = uint8array_of_bytes message
        val group = g
      end)

    method proposeRemoveMember g fp c =
      let fp = framing_params_of_js fp in
      let$ message, g = call_ce propose_remove_member g fp c in
      Js.some (object%js
        val message = uint8array_of_bytes message
        val group = g
      end)

    method proposeRemoveMyself g fp =
      let fp = framing_params_of_js fp in
      let$ message, g = call_ce propose_remove_myself g fp in
      Js.some (object%js
        val message = uint8array_of_bytes message
        val group = g
      end)

    method createCommit mls_group framing_params commit_params =
      (* mls_group is left "as is" and is not roundtripped via serialization *)
      let framing_params = framing_params_of_js framing_params in
      let commit_params = commit_params_of_js commit_params in
      let$ create_commit_result, mls_group = call_ce create_commit mls_group framing_params commit_params in
      Js.some object%js
        val create_commit_result_ = js_of_create_commit_result create_commit_result
        val group_ = mls_group
      end

    method createAddProposal kp =
      let* p = call_c create_add_proposal (bytes_of_uint8array kp) in
      Js.some p

    method createRemoveProposal group removed =
      let* p = call_c create_remove_proposal group removed in
      Js.some p

    method parseMessage msg_bytes =
      let* msg = call_c parse_message (bytes_of_uint8array msg_bytes) in
      Js.some (js_of_mls_message_nt msg)

    (* INTERNAL SELF-TEST *)

    method test: _ =
      MLS_Test_Internal.test ()

    (* OLD API BASED ON MLS.fst / MLS.ml -- TODO: REMOVE *)

    method currentEpoch (s: MLS.state) =
      Z.to_int (MLS.current_epoch s)

    method freshKeyPair1 (e: Typed_array.uint8Array Js.t) =
      let e = bytes_of_uint8array e in
      let* pub_key, priv_key = MLS.fresh_key_pair e in
      Js.some (object%js
        val pubKey = uint8array_of_bytes pub_key
        val privKey = priv_key
      end)

    method freshKeyPackage1 (e: Typed_array.uint8Array Js.t) (credential: _ Js.t) (priv: MLS.signature_key) =
      let e = bytes_of_uint8array e in
      let identity = bytes_of_js_string credential##.identity in
      let signature_key = bytes_of_uint8array credential##.signPubKey in
      let* key_package, hash, priv_key = MLS.fresh_key_package e { MLS.identity; signature_key } priv in
      Js.some (object%js
        val keyPackage = uint8array_of_bytes key_package
        val privKey = uint8array_of_bytes priv_key
        val hash = uint8array_of_bytes hash
      end)

    method create1 (e: Typed_array.uint8Array Js.t) (credential: _ Js.t) (priv: MLS.signature_key)
      (group_id: Js.js_string Js.t)
    =
      let e = bytes_of_uint8array e in
      let identity = bytes_of_js_string credential##.identity in
      let signature_key = bytes_of_uint8array credential##.signPubKey in
      let group_id = bytes_of_js_string group_id in
      (* Relying on the side-effect of printing errors *)
      let* s = MLS.create e { MLS.identity; signature_key } priv group_id in
      Js.some s

    method add1 (s: MLS.state) (key_package: Typed_array.uint8Array Js.t) (e: Typed_array.uint8Array Js.t) =
      let key_package = bytes_of_uint8array key_package in
      let e = bytes_of_uint8array e in
      let* state, (group_message, welcome_message) = MLS.add s key_package e in
      Js.some (object%js
        val groupMessage = object%js
          val groupId = js_string_of_bytes (fst group_message)
          val payload = uint8array_of_bytes (snd group_message)
        end
        val welcomeMessage = object%js
          val identity = js_string_of_bytes (fst welcome_message)
          val payload = uint8array_of_bytes (snd welcome_message)
        end
        val state = state
      end)

    method send1 (s: MLS.state) (e: Typed_array.uint8Array Js.t) (data: Js.js_string Js.t) =
      let e = bytes_of_uint8array e in
      let data = bytes_of_js_string data in
      let* state, group_message = MLS.send s e data in
      Js.some (object%js
        val groupMessage = object%js
          val groupId = js_string_of_bytes (fst group_message)
          val payload = uint8array_of_bytes (snd group_message)
        end
        val state = state
      end)

    method processGroupMessage1 (s: MLS.state) (payload: Typed_array.uint8Array Js.t) =
      let payload = bytes_of_uint8array payload in
      let* state, outcome = MLS.process_group_message s payload in
      Js.some (object%js
        val outcome = match outcome with
          | MLS.MsgData data ->
              Obj.magic (object%js
                val kind = "data"
                val payload = js_string_of_bytes data
              end)
          | MLS.MsgAdd identity ->
              Obj.magic (object%js
                val kind = "add"
                val identity = js_string_of_bytes identity
              end)
          | MLS.MsgRemove identity ->
              Obj.magic (object%js
                val kind = "remove"
                val identity = js_string_of_bytes identity
              end)
        val state = state
      end)

    method processWelcomeMessage1 (payload: Typed_array.uint8Array Js.t) (keyPair: _ Js.t) (lookup: _ Js.t) =
      let payload = bytes_of_uint8array payload in
      let lookup hash =
        let priv: _ Js.Opt.t = Js.Unsafe.fun_call lookup [| Js.Unsafe.inject (uint8array_of_bytes hash) |] in
        let priv = Js.Opt.to_option priv in
        Option.map bytes_of_uint8array priv
      in
      let key_pair = bytes_of_uint8array keyPair##.pubKey, keyPair##.privKey in
      let* group_id, state = MLS.process_welcome_message (FStar_Seq_Base.empty (), payload) key_pair lookup in
      Js.some (object%js
        val groupId = js_string_of_bytes group_id
        val state = state
      end)
  end)

let _ =
  print_endline "...loaded"
