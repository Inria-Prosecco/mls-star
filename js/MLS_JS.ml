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
  padding_size = Z.of_int o##.padding_size;
  authenticated_data = bytes_of_uint8array o##.authenticated_data;
}

let leaf_node_params_of_js o =
  { nothing_yet = () }

let commit_params_of_js o =
  let proposals = Array.to_list o##.proposals in
  let inline_tree = o##.inline_tree in
  let force_update = o##.force_update in
  let leaf_node_params = leaf_node_params_of_js o##.leaf_node_params in
  { proposals; inline_tree; force_update; leaf_node_params }

let js_of_create_commit_result { commit; welcome; group_info } = object%js
  val commit = uint8array_of_bytes commit
  val welcome = Js.Opt.option (Option.map uint8array_of_bytes welcome)
  val group_info = uint8array_of_bytes group_info
end

let js_of_create_key_package_result { key_package; keystore_key; keystore_value } = object%js
  val key_package = uint8array_of_bytes key_package
  val keystore_key_ = uint8array_of_bytes keystore_key
  val keystore_value_ = uint8array_of_bytes keystore_value
end

let js_of_processed_message { group_id; epoch; sender; authenticated_data1; content } = object%js
  val group_id = uint8array_of_bytes group_id
  val epoch = 0 (* TODO *)
  val sender = sender (* TODO *)
  val authenticated_data = uint8array_of_bytes authenticated_data1
  val content = content
end

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
      match Js.to_string cs with
      | _ ->
          (* TODO: actually offer more ciphersuites *)
          if !crypto_bytes_ <> None then
            print_and_fail "Cannot dynamically change ciphersuites";
          crypto_bytes_ := Some MLS_Crypto_Builtins.(mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519)

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
      let chain = List.map bytes_of_uint8array (Array.to_list chain) in
      let* cp = call_c mk_x509_credential kp chain in
      Js.some cp

    method getPublicCredential cp =
      let c = call_c get_public_credential cp in
      Js.some c

    method createKeyPackage cp =
      let$ ckpr = call_ce create_key_package cp in
      Js.some ckpr

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
      Js.some (Array.of_list r)

    method getNewCredential uv =
      let* r = call_c get_new_credential uv in
      Js.some (Js.Opt.option r)

    method processMessage g bytes =
      let bytes = bytes_of_uint8array bytes in
      let* pm, g = call_c process_message g bytes in
      Js.some (object%js
        val processed_message = js_of_processed_message pm
        val group = g
      end)

    method iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheCommit uv =
      Js.some (i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit uv)

    method mergeCommit g vc =
      let* g = call_c merge_commit g vc in
      Js.some g

    method iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheProposal up =
      Js.some (i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal up)

    method queueNewProposal g vp =
      let* g = call_c queue_new_proposal g vp in
      Js.some g

    method sendApplicationMessage g fp m =
      let fp = framing_params_of_js fp in
      let m = bytes_of_uint8array m in
      let$ message, g = call_ce g fp m in
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
        val create_commit_result = js_of_create_commit_result create_commit_result
        val mls_group = mls_group
      end

    method createAddProposal kp =
      let* p = call_c create_add_proposal (bytes_of_uint8array kp) in
      Js.some p

    method createRemoveProposal group removed =
      let* p = call_c create_remove_proposal group removed in
      Js.some p

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
