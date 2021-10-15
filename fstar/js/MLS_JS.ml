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

let byte_length (a: Typed_array.uint8Array Js.t) =
  let a = Obj.magic a in
  a##.byteLength

let bytes_of_uint8array (a: Typed_array.uint8Array Js.t) =
  let l = byte_length a in
  Printf.printf "byte length %d\n" l;
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
      | Success (key_package, priv_key) ->
          Js.some (object%js
            val keyPackage = key_package
            val privKey = uint8array_of_bytes priv_key
          end)
      | InternalError s ->
          print_endline ("InternalError: " ^ s);
          Js.null
      | ProtocolError s ->
          print_endline ("ProtocolError: " ^ s);
          Js.null

    method currentEpoch (s: MLS.state) =
      Z.to_int s.MLS.tree_state.MLS_TreeSync_Types.version3

    method create (e: Typed_array.uint8Array Js.t) (credential: _ Js.t) (priv: Typed_array.uint8Array Js.t)
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
  end)

let _ =
  print_endline "...loaded"
