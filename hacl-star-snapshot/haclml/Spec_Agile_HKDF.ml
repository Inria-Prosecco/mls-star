open Prims
type 'l lbytes = Spec_Hash_Definitions.bytes
let (extract_ikm_length_pred :
  Spec_Hash_Definitions.hash_alg -> Prims.nat -> Prims.bool) =
  fun a ->
    fun ikm_length ->
      Spec_Hash_Definitions.less_than_max_input_length
        (ikm_length + (Spec_Hash_Definitions.block_length a)) a
let (extract :
  Spec_Hash_Definitions.fixed_len_alg ->
    Spec_Hash_Definitions.bytes -> Spec_Hash_Definitions.bytes -> unit lbytes)
  = Spec_Agile_HMAC.hmac
let (expand_info_length_pred :
  Spec_Hash_Definitions.fixed_len_alg -> Prims.int -> Prims.bool) =
  fun a ->
    fun info_length ->
      Spec_Hash_Definitions.less_than_max_input_length
        ((((Spec_Hash_Definitions.hash_length a) + info_length) +
            Prims.int_one)
           + (Spec_Hash_Definitions.block_length a)) a
let (expand_output_length_pred :
  Spec_Hash_Definitions.fixed_len_alg -> Prims.int -> Prims.bool) =
  fun a ->
    fun len ->
      len <= ((Prims.of_int (255)) * (Spec_Hash_Definitions.hash_length a))
type ('a, 'i) a_spec = (FStar_UInt8.t, unit) Lib_Sequence.lseq
let (expand_loop :
  Spec_Hash_Definitions.fixed_len_alg ->
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
  Spec_Hash_Definitions.fixed_len_alg ->
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