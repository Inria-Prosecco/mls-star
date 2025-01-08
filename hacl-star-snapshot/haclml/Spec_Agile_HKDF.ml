open Prims
type 'l lbytes = Spec_Hash_Definitions.bytes
let (extract_ikm_length_pred :
  Spec_Hash_Definitions.hash_alg -> Prims.nat -> Prims.bool) =
  fun a ->
    fun ikm_length ->
      (ikm_length + (Spec_Hash_Definitions.block_length a)) <=
        (match a with
         | Spec_Hash_Definitions.MD5 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA1 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_224 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_256 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_384 ->
             (Prims.pow2 (Prims.of_int (125))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_512 ->
             (Prims.pow2 (Prims.of_int (125))) - Prims.int_one
         | Spec_Hash_Definitions.Blake2S ->
             (Prims.pow2 (Prims.of_int (64))) - Prims.int_one
         | Spec_Hash_Definitions.Blake2B ->
             (Prims.pow2 (Prims.of_int (128))) - Prims.int_one)
let (extract :
  Spec_Hash_Definitions.hash_alg ->
    Spec_Hash_Definitions.bytes -> Spec_Hash_Definitions.bytes -> unit lbytes)
  = Spec_Agile_HMAC.hmac

let extract a salt ikm =
  let open Spec_Hash_Definitions in
  match a with
  | SHA2_256 ->
      Primitives.hkdf_sha2_256_extract ~salt ~ikm
  | _ ->
      extract a salt ikm

let (expand_info_length_pred :
  Spec_Hash_Definitions.hash_alg -> Prims.int -> Prims.bool) =
  fun a ->
    fun info_length ->
      ((((Spec_Hash_Definitions.hash_length a) + info_length) + Prims.int_one)
         + (Spec_Hash_Definitions.block_length a))
        <=
        (match a with
         | Spec_Hash_Definitions.MD5 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA1 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_224 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_256 ->
             (Prims.pow2 (Prims.of_int (61))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_384 ->
             (Prims.pow2 (Prims.of_int (125))) - Prims.int_one
         | Spec_Hash_Definitions.SHA2_512 ->
             (Prims.pow2 (Prims.of_int (125))) - Prims.int_one
         | Spec_Hash_Definitions.Blake2S ->
             (Prims.pow2 (Prims.of_int (64))) - Prims.int_one
         | Spec_Hash_Definitions.Blake2B ->
             (Prims.pow2 (Prims.of_int (128))) - Prims.int_one)
let (expand_output_length_pred :
  Spec_Hash_Definitions.hash_alg -> Prims.int -> Prims.bool) =
  fun a ->
    fun len ->
      len <= ((Prims.of_int (255)) * (Spec_Hash_Definitions.hash_length a))
type ('a, 'i) a_spec = (FStar_UInt8.t, unit) Lib_Sequence.lseq
let (expand_loop :
  Spec_Hash_Definitions.hash_alg ->
    Spec_Hash_Definitions.bytes ->
      Spec_Hash_Definitions.bytes ->
        Prims.int ->
          Prims.int ->
            (unit, unit) a_spec ->
              ((unit, unit) a_spec * (FStar_UInt8.t, unit) Lib_Sequence.lseq))
  =
  fun a ->
    fun prk ->
      fun info ->
        fun n ->
          fun i ->
            fun tag ->
              let t =
                Spec_Agile_HMAC.hmac a prk
                  (FStar_Seq_Base.op_At_Bar tag
                     (FStar_Seq_Base.op_At_Bar info
                        (Lib_Sequence.create Prims.int_one
                           (FStar_UInt8.uint_to_t (i + Prims.int_one))))) in
              (t, t)
let (expand :
  Spec_Hash_Definitions.hash_alg ->
    Spec_Hash_Definitions.bytes ->
      Spec_Hash_Definitions.bytes -> Prims.int -> unit lbytes)
  =
  fun a ->
    fun prk ->
      fun info ->
        fun len ->
          let tlen = Spec_Hash_Definitions.hash_length a in
          let n = len / tlen in
          let uu___ =
            Obj.magic
              (Lib_Sequence.generate_blocks tlen n n ()
                 (fun uu___2 ->
                    fun uu___1 ->
                      (Obj.magic (expand_loop a prk info n)) uu___2 uu___1)
                 (Obj.magic (FStar_Seq_Base.empty ()))) in
          match uu___ with
          | (tag, output) ->
              if (n * tlen) < len
              then
                let t =
                  Spec_Agile_HMAC.hmac a prk
                    (FStar_Seq_Base.op_At_Bar tag
                       (FStar_Seq_Base.op_At_Bar info
                          (Lib_Sequence.create Prims.int_one
                             (FStar_UInt8.uint_to_t (n + Prims.int_one))))) in
                FStar_Seq_Base.op_At_Bar output
                  (Lib_Sequence.sub tlen t Prims.int_zero (len - (n * tlen)))
              else output

let expand a prk info size =
  let open Spec_Hash_Definitions in
  match a with
  | SHA2_256 ->
      Primitives.hkdf_sha2_256_expand ~prk ~info ~size
  | _ ->
      expand a prk info size

