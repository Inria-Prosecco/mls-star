open Prims
let coerce : 'b 'a . 'a -> 'b = fun uu___ -> (fun x -> Obj.magic x) uu___
let (init :
  Spec_Hash_Definitions.hash_alg -> unit Spec_Hash_Definitions.init_t) =
  fun uu___ ->
    (fun a ->
       match a with
       | Spec_Hash_Definitions.SHA2_224 ->
           Obj.magic (Obj.repr (Spec_SHA2.init a))
       | Spec_Hash_Definitions.SHA2_256 ->
           Obj.magic (Obj.repr (Spec_SHA2.init a))
       | Spec_Hash_Definitions.SHA2_384 ->
           Obj.magic (Obj.repr (Spec_SHA2.init a))
       | Spec_Hash_Definitions.SHA2_512 ->
           Obj.magic (Obj.repr (Spec_SHA2.init a))
       | Spec_Hash_Definitions.MD5 -> Obj.magic (Obj.repr Spec_MD5.init)
       | Spec_Hash_Definitions.SHA1 -> Obj.magic (Obj.repr Spec_SHA1.init)
       | Spec_Hash_Definitions.Blake2S ->
           Obj.magic
             (Obj.repr
                (Spec_Blake2.blake2_init_hash Spec_Blake2_Definitions.Blake2S
                   (Spec_Blake2_Definitions.blake2_default_params
                      Spec_Blake2_Definitions.Blake2S)))
       | Spec_Hash_Definitions.Blake2B ->
           Obj.magic
             (Obj.repr
                (Spec_Blake2.blake2_init_hash Spec_Blake2_Definitions.Blake2B
                   (Spec_Blake2_Definitions.blake2_default_params
                      Spec_Blake2_Definitions.Blake2B)))
       | Spec_Hash_Definitions.SHA3_224 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero))))
       | Spec_Hash_Definitions.SHA3_256 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero))))
       | Spec_Hash_Definitions.SHA3_384 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero))))
       | Spec_Hash_Definitions.SHA3_512 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero))))
       | Spec_Hash_Definitions.Shake128 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero))))
       | Spec_Hash_Definitions.Shake256 ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.create (Prims.of_int (25))
                   (Obj.magic (FStar_UInt64.uint_to_t Prims.int_zero)))))
      uu___
let (init_extra_state : Spec_Hash_Definitions.hash_alg -> Obj.t) =
  fun a ->
    match a with
    | Spec_Hash_Definitions.Blake2B -> Obj.repr Prims.int_zero
    | Spec_Hash_Definitions.Blake2S -> Obj.repr Prims.int_zero
    | uu___ -> Obj.repr ()
let (update :
  Spec_Hash_Definitions.md_alg -> unit Spec_Hash_Definitions.update_t) =
  fun a ->
    match a with
    | Spec_Hash_Definitions.SHA2_224 -> Spec_SHA2.update a
    | Spec_Hash_Definitions.SHA2_256 -> Spec_SHA2.update a
    | Spec_Hash_Definitions.SHA2_384 -> Spec_SHA2.update a
    | Spec_Hash_Definitions.SHA2_512 -> Spec_SHA2.update a
    | Spec_Hash_Definitions.MD5 -> Spec_MD5.update
    | Spec_Hash_Definitions.SHA1 -> Spec_SHA1.update
let (update_multi_pre :
  Spec_Hash_Definitions.hash_alg ->
    Obj.t -> Spec_Hash_Definitions.bytes -> Prims.bool)
  =
  fun a ->
    fun prev ->
      fun blocks ->
        match a with
        | Spec_Hash_Definitions.Blake2B ->
            Spec_Hash_Definitions.less_than_max_input_length
              ((FStar_Seq_Base.length blocks) + (Obj.magic prev)) a
        | Spec_Hash_Definitions.Blake2S ->
            Spec_Hash_Definitions.less_than_max_input_length
              ((FStar_Seq_Base.length blocks) + (Obj.magic prev)) a
        | uu___ -> true
let (update_multi :
  Spec_Hash_Definitions.hash_alg ->
    (Obj.t, unit) Lib_Sequence.lseq ->
      Obj.t ->
        unit Spec_Hash_Definitions.bytes_blocks ->
          (Obj.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun hash ->
      fun prev ->
        fun blocks ->
          match a with
          | Spec_Hash_Definitions.MD5 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.SHA1 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.SHA2_224 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.SHA2_256 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.SHA2_384 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.SHA2_512 ->
              Lib_UpdateMulti.mk_update_multi
                (Spec_Hash_Definitions.block_length a) (update a) hash blocks
          | Spec_Hash_Definitions.Blake2B ->
              let nb =
                (FStar_Seq_Base.length blocks) /
                  (Spec_Hash_Definitions.block_length a) in
              let a' =
                match a with
                | Spec_Hash_Definitions.Blake2S ->
                    Spec_Blake2_Definitions.Blake2S
                | Spec_Hash_Definitions.Blake2B ->
                    Spec_Blake2_Definitions.Blake2B in
              Lib_LoopCombinators.repeati nb
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic
                        (Spec_Blake2.blake2_update1 a' (Obj.magic prev)
                           blocks)) uu___1 uu___) hash
          | Spec_Hash_Definitions.Blake2S ->
              let nb =
                (FStar_Seq_Base.length blocks) /
                  (Spec_Hash_Definitions.block_length a) in
              let a' =
                match a with
                | Spec_Hash_Definitions.Blake2S ->
                    Spec_Blake2_Definitions.Blake2S
                | Spec_Hash_Definitions.Blake2B ->
                    Spec_Blake2_Definitions.Blake2B in
              Lib_LoopCombinators.repeati nb
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic
                        (Spec_Blake2.blake2_update1 a' (Obj.magic prev)
                           blocks)) uu___1 uu___) hash
          | Spec_Hash_Definitions.SHA3_224 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
          | Spec_Hash_Definitions.SHA3_256 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
          | Spec_Hash_Definitions.SHA3_384 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
          | Spec_Hash_Definitions.SHA3_512 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
          | Spec_Hash_Definitions.Shake128 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
          | Spec_Hash_Definitions.Shake256 ->
              let rateInBytes =
                (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
              Lib_Sequence.repeat_blocks_multi rateInBytes blocks
                (fun uu___1 ->
                   fun uu___ ->
                     (Obj.magic (Spec_SHA3.absorb_inner rateInBytes)) uu___1
                       uu___) hash
let (finish_md :
  Spec_Hash_Definitions.md_alg ->
    (Obj.t, unit) Lib_Sequence.lseq -> unit Spec_Hash_Definitions.bytes_hash)
  =
  fun a ->
    fun hashw ->
      let hash_final_w =
        FStar_Seq_Base.slice hashw Prims.int_zero
          (match a with
           | Spec_Hash_Definitions.MD5 -> (Prims.of_int (4))
           | Spec_Hash_Definitions.SHA1 -> (Prims.of_int (5))
           | Spec_Hash_Definitions.SHA2_224 -> (Prims.of_int (7))
           | Spec_Hash_Definitions.SHA2_256 -> (Prims.of_int (8))
           | Spec_Hash_Definitions.SHA2_384 -> (Prims.of_int (6))
           | Spec_Hash_Definitions.SHA2_512 -> (Prims.of_int (8))) in
      Spec_Hash_Definitions.bytes_of_words a
        (match a with
         | Spec_Hash_Definitions.MD5 -> (Prims.of_int (4))
         | Spec_Hash_Definitions.SHA1 -> (Prims.of_int (5))
         | Spec_Hash_Definitions.SHA2_224 -> (Prims.of_int (7))
         | Spec_Hash_Definitions.SHA2_256 -> (Prims.of_int (8))
         | Spec_Hash_Definitions.SHA2_384 -> (Prims.of_int (6))
         | Spec_Hash_Definitions.SHA2_512 -> (Prims.of_int (8))) hash_final_w
let (finish_blake :
  Spec_Hash_Definitions.blake_alg ->
    (Obj.t, unit) Lib_Sequence.lseq -> unit Spec_Hash_Definitions.bytes_hash)
  =
  fun a ->
    fun hash ->
      let alg =
        match a with
        | Spec_Hash_Definitions.Blake2S -> Spec_Blake2_Definitions.Blake2S
        | Spec_Hash_Definitions.Blake2B -> Spec_Blake2_Definitions.Blake2B in
      Spec_Blake2.blake2_finish alg (Obj.magic hash)
        (match alg with
         | Spec_Blake2_Definitions.Blake2S -> (Prims.of_int (32))
         | Spec_Blake2_Definitions.Blake2B -> (Prims.of_int (64)))
let (finish_sha3 :
  Spec_Hash_Definitions.keccak_alg ->
    (Obj.t, unit) Lib_Sequence.lseq ->
      Obj.t -> (unit, unit) Spec_Hash_Definitions.bytes_hash')
  =
  fun a ->
    fun s ->
      fun l ->
        let rateInBytes = (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
        match a with
        | Spec_Hash_Definitions.SHA3_224 ->
            let rateInBytes1 =
              (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
            let outputByteLen = Spec_Hash_Definitions.hash_length a in
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes1 outputByteLen
        | Spec_Hash_Definitions.SHA3_256 ->
            let rateInBytes1 =
              (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
            let outputByteLen = Spec_Hash_Definitions.hash_length a in
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes1 outputByteLen
        | Spec_Hash_Definitions.SHA3_384 ->
            let rateInBytes1 =
              (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
            let outputByteLen = Spec_Hash_Definitions.hash_length a in
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes1 outputByteLen
        | Spec_Hash_Definitions.SHA3_512 ->
            let rateInBytes1 =
              (Spec_Hash_Definitions.rate a) / (Prims.of_int (8)) in
            let outputByteLen = Spec_Hash_Definitions.hash_length a in
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes1 outputByteLen
        | Spec_Hash_Definitions.Shake128 ->
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes (Obj.magic l)
        | Spec_Hash_Definitions.Shake256 ->
            Spec_SHA3.squeeze (Obj.magic s) rateInBytes (Obj.magic l)
let (finish :
  Spec_Hash_Definitions.hash_alg -> unit Spec_Hash_Definitions.finish_t) =
  fun a ->
    fun hashw ->
      fun l ->
        if
          match a with
          | Spec_Hash_Definitions.Blake2S -> true
          | Spec_Hash_Definitions.Blake2B -> true
          | uu___ -> false
        then finish_blake a hashw
        else
          if
            (match a with
             | Spec_Hash_Definitions.SHA3_224 -> true
             | Spec_Hash_Definitions.SHA3_256 -> true
             | Spec_Hash_Definitions.SHA3_384 -> true
             | Spec_Hash_Definitions.SHA3_512 -> true
             | Spec_Hash_Definitions.Shake128 -> true
             | Spec_Hash_Definitions.Shake256 -> true
             | uu___1 -> false)
          then finish_sha3 a hashw l
          else finish_md a hashw
let (hash' :
  Spec_Hash_Definitions.hash_alg ->
    Spec_Hash_Definitions.bytes ->
      Obj.t -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun input ->
      fun l ->
        if
          match a with
          | Spec_Hash_Definitions.Blake2S -> true
          | Spec_Hash_Definitions.Blake2B -> true
          | uu___ -> false
        then
          Spec_Blake2.blake2
            (match a with
             | Spec_Hash_Definitions.Blake2S ->
                 Spec_Blake2_Definitions.Blake2S
             | Spec_Hash_Definitions.Blake2B ->
                 Spec_Blake2_Definitions.Blake2B) false input
            (Spec_Blake2_Definitions.blake2_default_params
               (match a with
                | Spec_Hash_Definitions.Blake2S ->
                    Spec_Blake2_Definitions.Blake2S
                | Spec_Hash_Definitions.Blake2B ->
                    Spec_Blake2_Definitions.Blake2B))
            (FStar_Seq_Base.empty ())
        else
          if
            (match a with
             | Spec_Hash_Definitions.MD5 -> true
             | Spec_Hash_Definitions.SHA1 -> true
             | Spec_Hash_Definitions.SHA2_224 -> true
             | Spec_Hash_Definitions.SHA2_256 -> true
             | Spec_Hash_Definitions.SHA2_384 -> true
             | Spec_Hash_Definitions.SHA2_512 -> true
             | uu___1 -> false)
          then
            (let padding = Spec_Hash_MD.pad a (FStar_Seq_Base.length input) in
             finish_md a
               (update_multi a (init a) (Obj.repr ())
                  (FStar_Seq_Base.op_At_Bar input padding)))
          else
            (match a with
             | Spec_Hash_Definitions.SHA3_224 ->
                 Spec_SHA3.sha3_224 (FStar_Seq_Base.length input) input
             | Spec_Hash_Definitions.SHA3_256 ->
                 Spec_SHA3.sha3_256 (FStar_Seq_Base.length input) input
             | Spec_Hash_Definitions.SHA3_384 ->
                 Spec_SHA3.sha3_384 (FStar_Seq_Base.length input) input
             | Spec_Hash_Definitions.SHA3_512 ->
                 Spec_SHA3.sha3_512 (FStar_Seq_Base.length input) input
             | Spec_Hash_Definitions.Shake128 ->
                 Spec_SHA3.shake128 (FStar_Seq_Base.length input) input
                   (Obj.magic l)
             | Spec_Hash_Definitions.Shake256 ->
                 Spec_SHA3.shake256 (FStar_Seq_Base.length input) input
                   (Obj.magic l))
let (hash :
  Spec_Hash_Definitions.fixed_len_alg ->
    Spec_Hash_Definitions.bytes -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  = fun a -> fun input -> hash' a input (Obj.repr ())