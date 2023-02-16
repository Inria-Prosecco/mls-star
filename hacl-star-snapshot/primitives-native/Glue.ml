(* Branch protz_seq_parray, using JCF's persistent array module *)
(*
  let bytes_of_seq8 s =
    let a = FStar_Seq_Base.PArray.to_array s in
    let data = Bytes.create (Array.length a) in
    Array.iteri (Bytes.set_uint8 data) a;
    data

  let seq8_of_bytes b =
    FStar_Seq_Base.PArray.init (Bytes.length b)
      (fun i -> Char.code (Bytes.get b i))
*)

let bytes_of_seq8 s =
  let FStar_Seq_Base.MkSeq l = s in
  let data = Bytes.create (List.length l) in
  List.iteri (Bytes.set_uint8 data) l;
  data

let seq8_of_bytes b =
  FStar_Seq_Base.MkSeq (
    List.init (Bytes.length b) (Bytes.get_uint8 b)
)
