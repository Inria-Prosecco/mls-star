open Prims
type hash_alg =
  | SHA2_224 
  | SHA2_256 
  | SHA2_384 
  | SHA2_512 
  | SHA1 
  | MD5 
  | Blake2S 
  | Blake2B 
  | SHA3_256 
  | SHA3_224 
  | SHA3_384 
  | SHA3_512 
  | Shake128 
  | Shake256 
let (uu___is_SHA2_224 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA2_224 -> true | uu___ -> false
let (uu___is_SHA2_256 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA2_256 -> true | uu___ -> false
let (uu___is_SHA2_384 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA2_384 -> true | uu___ -> false
let (uu___is_SHA2_512 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA2_512 -> true | uu___ -> false
let (uu___is_SHA1 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA1 -> true | uu___ -> false
let (uu___is_MD5 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | MD5 -> true | uu___ -> false
let (uu___is_Blake2S : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | Blake2S -> true | uu___ -> false
let (uu___is_Blake2B : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | Blake2B -> true | uu___ -> false
let (uu___is_SHA3_256 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA3_256 -> true | uu___ -> false
let (uu___is_SHA3_224 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA3_224 -> true | uu___ -> false
let (uu___is_SHA3_384 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA3_384 -> true | uu___ -> false
let (uu___is_SHA3_512 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | SHA3_512 -> true | uu___ -> false
let (uu___is_Shake128 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | Shake128 -> true | uu___ -> false
let (uu___is_Shake256 : hash_alg -> Prims.bool) =
  fun projectee -> match projectee with | Shake256 -> true | uu___ -> false
type sha2_alg = hash_alg
type keccak_alg = hash_alg
type blake_alg = hash_alg
type md_alg = hash_alg
type fixed_len_alg = hash_alg
let (to_blake_alg : blake_alg -> Spec_Blake2_Definitions.alg) =
  fun a ->
    match a with
    | Blake2S -> Spec_Blake2_Definitions.Blake2S
    | Blake2B -> Spec_Blake2_Definitions.Blake2B
let (to_hash_alg : Spec_Blake2_Definitions.alg -> hash_alg) =
  fun a ->
    match a with
    | Spec_Blake2_Definitions.Blake2S -> Blake2S
    | Spec_Blake2_Definitions.Blake2B -> Blake2B
let (max_input_length : hash_alg -> Prims.pos FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | MD5 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
    | SHA1 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
    | SHA2_224 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
    | SHA2_256 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
    | SHA2_384 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (125))) - Prims.int_one)
    | SHA2_512 ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (125))) - Prims.int_one)
    | Blake2S ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (64))) - Prims.int_one)
    | Blake2B ->
        FStar_Pervasives_Native.Some
          ((Prims.pow2 (Prims.of_int (128))) - Prims.int_one)
    | SHA3_224 -> FStar_Pervasives_Native.None
    | SHA3_256 -> FStar_Pervasives_Native.None
    | SHA3_384 -> FStar_Pervasives_Native.None
    | SHA3_512 -> FStar_Pervasives_Native.None
    | Shake128 -> FStar_Pervasives_Native.None
    | Shake256 -> FStar_Pervasives_Native.None
type maxed_hash_alg = hash_alg
let (len_int_type : maxed_hash_alg -> Lib_IntTypes.inttype) =
  fun uu___ ->
    match uu___ with
    | MD5 -> Lib_IntTypes.U64
    | SHA1 -> Lib_IntTypes.U64
    | SHA2_224 -> Lib_IntTypes.U64
    | SHA2_256 -> Lib_IntTypes.U64
    | SHA2_384 -> Lib_IntTypes.U128
    | SHA2_512 -> Lib_IntTypes.U128
    | Blake2S -> Lib_IntTypes.U64
    | Blake2B -> Lib_IntTypes.U128
let (nat_to_len : maxed_hash_alg -> Prims.nat -> Obj.t) =
  fun a ->
    fun n ->
      Lib_IntTypes.mk_int
        (match a with
         | MD5 -> Lib_IntTypes.U64
         | SHA1 -> Lib_IntTypes.U64
         | SHA2_224 -> Lib_IntTypes.U64
         | SHA2_256 -> Lib_IntTypes.U64
         | SHA2_384 -> Lib_IntTypes.U128
         | SHA2_512 -> Lib_IntTypes.U128
         | Blake2S -> Lib_IntTypes.U64
         | Blake2B -> Lib_IntTypes.U128) Lib_IntTypes.PUB n
type 'uuuuu len_t = Obj.t
let (len_v : maxed_hash_alg -> Obj.t -> Prims.nat) =
  fun uu___1 ->
    fun uu___ ->
      (fun uu___ ->
         match uu___ with
         | MD5 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U64 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | SHA1 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U64 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | SHA2_224 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U64 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | SHA2_256 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U64 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | SHA2_384 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U128 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | SHA2_512 ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U128 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | Blake2S ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U64 Lib_IntTypes.PUB
                       (Obj.magic u)))
         | Blake2B ->
             Obj.magic
               (Obj.repr
                  (fun u ->
                     Lib_IntTypes.v Lib_IntTypes.U128 Lib_IntTypes.PUB
                       (Obj.magic u)))) uu___1 uu___
let (len_length : maxed_hash_alg -> Prims.nat) =
  fun uu___ ->
    match uu___ with
    | MD5 -> (Prims.of_int (8))
    | SHA1 -> (Prims.of_int (8))
    | SHA2_224 -> (Prims.of_int (8))
    | SHA2_256 -> (Prims.of_int (8))
    | SHA2_384 -> (Prims.of_int (16))
    | SHA2_512 -> (Prims.of_int (16))
    | Blake2S -> (Prims.of_int (8))
    | Blake2B -> (Prims.of_int (16))
let (len_len : maxed_hash_alg -> FStar_UInt32.t) =
  fun uu___ ->
    match uu___ with
    | MD5 -> (Stdint.Uint32.of_int (8))
    | SHA1 -> (Stdint.Uint32.of_int (8))
    | SHA2_224 -> (Stdint.Uint32.of_int (8))
    | SHA2_256 -> (Stdint.Uint32.of_int (8))
    | SHA2_384 -> (Stdint.Uint32.of_int (16))
    | SHA2_512 -> (Stdint.Uint32.of_int (16))
    | Blake2S -> (Stdint.Uint32.of_int (8))
    | Blake2B -> (Stdint.Uint32.of_int (16))
let (word_t : hash_alg -> Lib_IntTypes.inttype) =
  fun uu___ ->
    match uu___ with
    | MD5 -> Lib_IntTypes.U32
    | SHA1 -> Lib_IntTypes.U32
    | SHA2_224 -> Lib_IntTypes.U32
    | SHA2_256 -> Lib_IntTypes.U32
    | SHA2_384 -> Lib_IntTypes.U64
    | SHA2_512 -> Lib_IntTypes.U64
    | Blake2S -> Lib_IntTypes.U32
    | Blake2B -> Lib_IntTypes.U64
    | SHA3_224 -> Lib_IntTypes.U64
    | SHA3_256 -> Lib_IntTypes.U64
    | SHA3_384 -> Lib_IntTypes.U64
    | SHA3_512 -> Lib_IntTypes.U64
    | Shake128 -> Lib_IntTypes.U64
    | Shake256 -> Lib_IntTypes.U64
type 'a row = (Obj.t, unit) Lib_Sequence.lseq
type 'a word = Obj.t
let (word_length : hash_alg -> Prims.nat) =
  fun uu___ ->
    match uu___ with
    | MD5 -> (Prims.of_int (4))
    | SHA1 -> (Prims.of_int (4))
    | SHA2_224 -> (Prims.of_int (4))
    | SHA2_256 -> (Prims.of_int (4))
    | SHA2_384 -> (Prims.of_int (8))
    | SHA2_512 -> (Prims.of_int (8))
    | SHA3_224 -> (Prims.of_int (8))
    | SHA3_256 -> (Prims.of_int (8))
    | SHA3_384 -> (Prims.of_int (8))
    | SHA3_512 -> (Prims.of_int (8))
    | Shake128 -> (Prims.of_int (8))
    | Shake256 -> (Prims.of_int (8))
    | Blake2S -> (Prims.of_int (4))
    | Blake2B -> (Prims.of_int (8))
let (rate : keccak_alg -> Prims.nat) =
  fun a ->
    match a with
    | SHA3_224 -> (Prims.of_int (1152))
    | SHA3_256 -> (Prims.of_int (1088))
    | SHA3_384 -> (Prims.of_int (832))
    | SHA3_512 -> (Prims.of_int (576))
    | Shake128 -> (Prims.of_int (1344))
    | Shake256 -> (Prims.of_int (1088))
let (block_word_length : hash_alg -> Prims.int) =
  fun a ->
    match a with
    | SHA3_224 -> (Prims.of_int (18))
    | SHA3_256 -> (Prims.of_int (17))
    | SHA3_384 -> (Prims.of_int (13))
    | SHA3_512 -> (Prims.of_int (9))
    | Shake128 -> (Prims.of_int (21))
    | Shake256 -> (Prims.of_int (17))
    | MD5 -> (Prims.of_int (16))
    | SHA1 -> (Prims.of_int (16))
    | SHA2_224 -> (Prims.of_int (16))
    | SHA2_256 -> (Prims.of_int (16))
    | SHA2_384 -> (Prims.of_int (16))
    | SHA2_512 -> (Prims.of_int (16))
    | Blake2S -> (Prims.of_int (16))
    | Blake2B -> (Prims.of_int (16))
let (block_length : hash_alg -> Prims.nonzero) =
  fun a -> (word_length a) * (block_word_length a)
let (state_word_length : hash_alg -> Prims.int) =
  fun a ->
    match a with
    | MD5 -> (Prims.of_int (4))
    | SHA1 -> (Prims.of_int (5))
    | Blake2S -> (Prims.of_int (4))
    | Blake2B -> (Prims.of_int (4))
    | SHA3_224 -> (Prims.of_int (25))
    | SHA3_256 -> (Prims.of_int (25))
    | SHA3_384 -> (Prims.of_int (25))
    | SHA3_512 -> (Prims.of_int (25))
    | Shake128 -> (Prims.of_int (25))
    | Shake256 -> (Prims.of_int (25))
    | SHA2_224 -> (Prims.of_int (8))
    | SHA2_256 -> (Prims.of_int (8))
    | SHA2_384 -> (Prims.of_int (8))
    | SHA2_512 -> (Prims.of_int (8))
type 'a extra_state = Obj.t
type 'a words_state = (Obj.t, unit) Lib_Sequence.lseq
let (hash_word_length : md_alg -> Prims.nat) =
  fun uu___ ->
    match uu___ with
    | MD5 -> (Prims.of_int (4))
    | SHA1 -> (Prims.of_int (5))
    | SHA2_224 -> (Prims.of_int (7))
    | SHA2_256 -> (Prims.of_int (8))
    | SHA2_384 -> (Prims.of_int (6))
    | SHA2_512 -> (Prims.of_int (8))
let (hash_length : hash_alg -> Prims.nat) =
  fun a ->
    if
      match a with
      | MD5 -> true
      | SHA1 -> true
      | SHA2_224 -> true
      | SHA2_256 -> true
      | SHA2_384 -> true
      | SHA2_512 -> true
      | uu___ -> false
    then
      (word_length a) *
        (match a with
         | MD5 -> (Prims.of_int (4))
         | SHA1 -> (Prims.of_int (5))
         | SHA2_224 -> (Prims.of_int (7))
         | SHA2_256 -> (Prims.of_int (8))
         | SHA2_384 -> (Prims.of_int (6))
         | SHA2_512 -> (Prims.of_int (8)))
    else
      (match a with
       | SHA3_224 -> (Prims.of_int (28))
       | SHA3_256 -> (Prims.of_int (32))
       | SHA3_384 -> (Prims.of_int (48))
       | SHA3_512 -> (Prims.of_int (64))
       | Blake2S -> (Prims.of_int (32))
       | Blake2B -> (Prims.of_int (64)))
let (pad0_length : md_alg -> Prims.nat -> Prims.nat) =
  fun a ->
    fun len ->
      ((block_length a) - ((len + (len_length a)) + Prims.int_one)) mod
        (block_length a)
let (pad_length : md_alg -> Prims.nat -> Prims.nat) =
  fun a -> fun len -> ((pad0_length a len) + Prims.int_one) + (len_length a)
let (bytes_of_words :
  hash_alg ->
    Prims.nat ->
      (Obj.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           match uu___ with
           | MD5 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (4))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_le_inner
                                        Lib_IntTypes.U32 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))
           | SHA1 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (4))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_be_inner
                                        Lib_IntTypes.U32 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))
           | SHA2_224 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (4))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_be_inner
                                        Lib_IntTypes.U32 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))
           | SHA2_256 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (4))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_be_inner
                                        Lib_IntTypes.U32 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))
           | SHA2_384 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (8))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_be_inner
                                        Lib_IntTypes.U64 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))
           | SHA2_512 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun ul ->
                         let uu___1 =
                           Lib_Sequence.generate_blocks (Prims.of_int (8))
                             len len ()
                             (fun uu___3 ->
                                fun uu___2 ->
                                  (Obj.magic
                                     (Lib_ByteSequence.uints_to_bytes_be_inner
                                        Lib_IntTypes.U64 Lib_IntTypes.SEC len
                                        (Obj.magic ul))) uu___3 uu___2)
                             (Obj.repr ()) in
                         match uu___1 with | (uu___2, o) -> o))) uu___2
          uu___1 uu___
let (words_of_bytes :
  hash_alg ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (Obj.t, unit) Lib_Sequence.lseq)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           match uu___ with
           | MD5 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_le_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (4))) b
                                        (i * (Prims.of_int (4)))
                                        (Prims.of_int (4)))) in
                              FStar_UInt32.uint_to_t n)))
           | SHA1 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_be_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (4))) b
                                        (i * (Prims.of_int (4)))
                                        (Prims.of_int (4)))) in
                              FStar_UInt32.uint_to_t n)))
           | SHA2_224 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_be_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (4))) b
                                        (i * (Prims.of_int (4)))
                                        (Prims.of_int (4)))) in
                              FStar_UInt32.uint_to_t n)))
           | SHA2_256 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_be_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (4))) b
                                        (i * (Prims.of_int (4)))
                                        (Prims.of_int (4)))) in
                              FStar_UInt32.uint_to_t n)))
           | SHA2_384 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_be_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (8))) b
                                        (i * (Prims.of_int (8)))
                                        (Prims.of_int (8)))) in
                              FStar_UInt64.uint_to_t n)))
           | SHA2_512 ->
               Obj.magic
                 (Obj.repr
                    (fun len ->
                       fun b ->
                         Lib_Sequence.createi len
                           (fun i ->
                              let n =
                                Lib_ByteSequence.nat_from_intseq_be_
                                  Lib_IntTypes.U8 Lib_IntTypes.SEC
                                  (Obj.magic
                                     (Lib_Sequence.sub
                                        (len * (Prims.of_int (8))) b
                                        (i * (Prims.of_int (8)))
                                        (Prims.of_int (8)))) in
                              FStar_UInt64.uint_to_t n)))) uu___2 uu___1
          uu___
type bytes = FStar_UInt8.t FStar_Seq_Base.seq
type 'a bytes_block = bytes
type 'a bytes_blocks = bytes
type 'uuuuu output_length = Obj.t
let (hash_length' : hash_alg -> Obj.t -> Prims.nat) =
  fun uu___1 ->
    fun uu___ ->
      (fun a ->
         fun l ->
           if
             match a with
             | Shake128 -> true
             | Shake256 -> true
             | uu___ -> false
           then Obj.magic (Obj.repr l)
           else Obj.magic (Obj.repr (hash_length a))) uu___1 uu___
type 'a bytes_hash = bytes
type ('a, 'l) bytes_hash' = bytes
type 'a init_t = (Obj.t, unit) Lib_Sequence.lseq
type 'a update_t =
  (Obj.t, unit) Lib_Sequence.lseq -> bytes -> (Obj.t, unit) Lib_Sequence.lseq
let (less_than_max_input_length : Prims.int -> hash_alg -> Prims.bool) =
  fun l ->
    fun a ->
      match match a with
            | MD5 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
            | SHA1 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
            | SHA2_224 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
            | SHA2_256 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (61))) - Prims.int_one)
            | SHA2_384 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (125))) - Prims.int_one)
            | SHA2_512 ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (125))) - Prims.int_one)
            | Blake2S ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (64))) - Prims.int_one)
            | Blake2B ->
                FStar_Pervasives_Native.Some
                  ((Prims.pow2 (Prims.of_int (128))) - Prims.int_one)
            | SHA3_224 -> FStar_Pervasives_Native.None
            | SHA3_256 -> FStar_Pervasives_Native.None
            | SHA3_384 -> FStar_Pervasives_Native.None
            | SHA3_512 -> FStar_Pervasives_Native.None
            | Shake128 -> FStar_Pervasives_Native.None
            | Shake256 -> FStar_Pervasives_Native.None
      with
      | FStar_Pervasives_Native.Some max -> l <= max
      | FStar_Pervasives_Native.None -> true
type 'a pad_t = Prims.nat -> bytes
type 'a finish_t =
  (Obj.t, unit) Lib_Sequence.lseq -> Obj.t -> (unit, unit) bytes_hash'