open Js_of_ocaml

(* In spec-land, `FStar.Seq.seq FStar.UInt8.t` becomes this: *)
type bytes = int FStar_Seq_Base.seq

let list_of_bytes = FStar_Seq_Properties.seq_to_list

let bytes_of_list l =
  FStar_Seq_Base.MkSeq (List.map (fun x ->
    assert (x <= 255);
    x
  ) l)

let bytes_of_js_string (s: Js.js_string Js.t) =
  let s = Js.to_string s in
  bytes_of_list (List.map (fun x -> Char.code x) (List.of_seq (String.to_seq s)))

let js_string_of_bytes (b: bytes): Js.js_string Js.t =
  let FStar_Seq_Base.MkSeq b = b in
  Js.string (String.of_seq (Seq.map Char.chr (List.to_seq b)))

let byte_length (a: Typed_array.uint8Array Js.t) =
  let a = Obj.magic a in
  a##.byteLength

let bytes_of_uint8array (a: Typed_array.uint8Array Js.t) =
  let l = byte_length a in
  (* Printf.printf "byte length %d\n" l; *)
  FStar_Seq_Base.MkSeq (List.init l (fun i -> Typed_array.unsafe_get a i))

let uint8array_of_bytes (b: bytes) =
  let FStar_Seq_Base.MkSeq b = b in
  let l = List.length b in
  let a = new%js Typed_array.uint8Array l in
  List.iteri (Typed_array.set a) b;
  a

let _ =
  Js.export_all (object%js
    method test: _ =
      MLS_Test_Internal.test ()

    method freshKeyPair1 (e: Typed_array.uint8Array Js.t) =
      let e = bytes_of_uint8array e in
      match MLS.fresh_key_pair e with
      | Success (pub_key, priv_key) ->
          Js.some (object%js
            val pubKey = uint8array_of_bytes pub_key
            val privKey = uint8array_of_bytes priv_key
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method freshKeyPackage1 (e: Typed_array.uint8Array Js.t) (credential: _ Js.t) (priv: Typed_array.uint8Array Js.t) =
      let e = bytes_of_uint8array e in
      let identity = bytes_of_js_string credential##.identity in
      let signature_key = bytes_of_uint8array credential##.signPubKey in
      match MLS.fresh_key_package e { MLS.identity; signature_key } (bytes_of_uint8array priv) with
      | Success (key_package, hash, priv_key) ->
          Js.some (object%js
            val keyPackage = uint8array_of_bytes key_package
            val privKey = uint8array_of_bytes priv_key
            val hash = uint8array_of_bytes hash
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method currentEpoch (s: MLS.state) =
      Z.to_int s.MLS.tree_state.MLS_TreeSync_Types.version3

    method create1 (e: Typed_array.uint8Array Js.t) (credential: _ Js.t) (priv: Typed_array.uint8Array Js.t)
      (group_id: Js.js_string Js.t)
    =
      let e = bytes_of_uint8array e in
      let identity = bytes_of_js_string credential##.identity in
      let signature_key = bytes_of_uint8array credential##.signPubKey in
      let group_id = bytes_of_js_string group_id in
      let priv = bytes_of_uint8array priv in
      match MLS.create e { MLS.identity; signature_key } priv group_id with
      | Success s ->
          Js.some s
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method add1 (s: MLS.state) (key_package: Typed_array.uint8Array Js.t) (e: Typed_array.uint8Array Js.t) =
      let key_package = bytes_of_uint8array key_package in
      let e = bytes_of_uint8array e in
      match MLS.add s key_package e with
      | Success (state, (group_message, welcome_message)) ->
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
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method send1 (s: MLS.state) (e: Typed_array.uint8Array Js.t) (data: Js.js_string Js.t) =
      let e = bytes_of_uint8array e in
      let data = bytes_of_js_string data in
      match MLS.send s e data with
      | Success (state, group_message) ->
          Js.some (object%js
            val groupMessage = object%js
              val groupId = js_string_of_bytes (fst group_message)
              val payload = uint8array_of_bytes (snd group_message)
            end
            val state = state
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method processGroupMessage1 (s: MLS.state) (payload: Typed_array.uint8Array Js.t) =
      let payload = bytes_of_uint8array payload in
      match MLS.process_group_message s payload with
      | Success (state, outcome) ->
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
            val state = state
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method processWelcomeMessage1 (payload: Typed_array.uint8Array Js.t) (keyPair: _ Js.t) (lookup: _ Js.t) =
      let payload = bytes_of_uint8array payload in
      let lookup hash =
        let priv: _ Js.Opt.t = Js.Unsafe.fun_call lookup [| Js.Unsafe.inject (uint8array_of_bytes hash) |] in
        Option.map bytes_of_uint8array (Js.Opt.to_option priv)
      in
      let key_pair = bytes_of_uint8array keyPair##.pubKey, bytes_of_uint8array keyPair##.privKey in
      match MLS.process_welcome_message (FStar_Seq_Base.empty (), payload) key_pair lookup with
      | Success (group_id, state) ->
          Js.some (object%js
            val groupId = js_string_of_bytes group_id
            val state = state
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null
  end)

let _ =
  print_endline "...loaded"
