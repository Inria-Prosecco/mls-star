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
