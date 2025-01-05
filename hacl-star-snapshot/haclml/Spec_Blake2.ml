open Prims
let (serialize_blake2s_params :
  unit Spec_Blake2_Definitions.blake2_params ->
    (FStar_UInt32.t, unit) Lib_Sequence.lseq)
  =
  fun p ->
    let s0 =
      FStar_UInt32.logxor
        (FStar_UInt32.uint_to_t
           (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.PUB
              (Obj.magic p.Spec_Blake2_Definitions.digest_length)))
        (FStar_UInt32.logxor
           (FStar_UInt32.shift_left
              (FStar_UInt32.uint_to_t
                 (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.PUB
                    (Obj.magic p.Spec_Blake2_Definitions.key_length)))
              (FStar_UInt32.uint_to_t (Prims.of_int (8))))
           (FStar_UInt32.logxor
              (FStar_UInt32.shift_left
                 (FStar_UInt32.uint_to_t
                    (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                       (Obj.magic p.Spec_Blake2_Definitions.fanout)))
                 (FStar_UInt32.uint_to_t (Prims.of_int (16))))
              (FStar_UInt32.shift_left
                 (FStar_UInt32.uint_to_t
                    (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                       (Obj.magic p.Spec_Blake2_Definitions.depth)))
                 (FStar_UInt32.uint_to_t (Prims.of_int (24)))))) in
    let s1 = p.Spec_Blake2_Definitions.leaf_length in
    let s2 =
      FStar_Int_Cast.uint64_to_uint32 p.Spec_Blake2_Definitions.node_offset in
    let s3 =
      FStar_UInt32.logxor
        (FStar_Int_Cast.uint64_to_uint32
           (FStar_UInt64.shift_right p.Spec_Blake2_Definitions.node_offset
              (FStar_UInt32.uint_to_t (Prims.of_int (32)))))
        (FStar_UInt32.logxor
           (FStar_UInt32.shift_left
              (FStar_UInt32.uint_to_t
                 (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                    (Obj.magic p.Spec_Blake2_Definitions.node_depth)))
              (FStar_UInt32.uint_to_t (Prims.of_int (16))))
           (FStar_UInt32.shift_left
              (FStar_UInt32.uint_to_t
                 (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                    (Obj.magic p.Spec_Blake2_Definitions.inner_length)))
              (FStar_UInt32.uint_to_t (Prims.of_int (24))))) in
    let salt_u32 =
      Lib_Sequence.createi (Prims.of_int (2))
        (fun i ->
           let n =
             Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (Obj.magic
                  (Lib_Sequence.sub (Prims.of_int (8))
                     p.Spec_Blake2_Definitions.salt (i * (Prims.of_int (4)))
                     (Prims.of_int (4)))) in
           FStar_UInt32.uint_to_t n) in
    let s4 = Lib_Sequence.index (Prims.of_int (2)) salt_u32 Prims.int_zero in
    let s5 = Lib_Sequence.index (Prims.of_int (2)) salt_u32 Prims.int_one in
    let personal_u32 =
      Lib_Sequence.createi (Prims.of_int (2))
        (fun i ->
           let n =
             Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (Obj.magic
                  (Lib_Sequence.sub (Prims.of_int (8))
                     p.Spec_Blake2_Definitions.personal
                     (i * (Prims.of_int (4))) (Prims.of_int (4)))) in
           FStar_UInt32.uint_to_t n) in
    let s6 =
      Lib_Sequence.index (Prims.of_int (2)) personal_u32 Prims.int_zero in
    let s7 = Lib_Sequence.index (Prims.of_int (2)) personal_u32 Prims.int_one in
    Lib_Sequence.of_list [s0; s1; s2; s3; s4; s5; s6; s7]
let (serialize_blake2b_params :
  unit Spec_Blake2_Definitions.blake2_params ->
    (FStar_UInt64.t, unit) Lib_Sequence.lseq)
  =
  fun p ->
    let s0 =
      FStar_UInt64.logxor
        (FStar_UInt64.uint_to_t
           (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.PUB
              (Obj.magic p.Spec_Blake2_Definitions.digest_length)))
        (FStar_UInt64.logxor
           (FStar_UInt64.shift_left
              (FStar_UInt64.uint_to_t
                 (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.PUB
                    (Obj.magic p.Spec_Blake2_Definitions.key_length)))
              (FStar_UInt32.uint_to_t (Prims.of_int (8))))
           (FStar_UInt64.logxor
              (FStar_UInt64.shift_left
                 (FStar_UInt64.uint_to_t
                    (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                       (Obj.magic p.Spec_Blake2_Definitions.fanout)))
                 (FStar_UInt32.uint_to_t (Prims.of_int (16))))
              (FStar_UInt64.logxor
                 (FStar_UInt64.shift_left
                    (FStar_UInt64.uint_to_t
                       (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                          (Obj.magic p.Spec_Blake2_Definitions.depth)))
                    (FStar_UInt32.uint_to_t (Prims.of_int (24))))
                 (FStar_UInt64.shift_left
                    (FStar_UInt64.uint_to_t
                       (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.SEC
                          (Obj.magic p.Spec_Blake2_Definitions.leaf_length)))
                    (FStar_UInt32.uint_to_t (Prims.of_int (32))))))) in
    let s1 = p.Spec_Blake2_Definitions.node_offset in
    let s2 =
      FStar_UInt64.logxor
        (FStar_UInt64.uint_to_t
           (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
              (Obj.magic p.Spec_Blake2_Definitions.node_depth)))
        (FStar_UInt64.shift_left
           (FStar_UInt64.uint_to_t
              (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                 (Obj.magic p.Spec_Blake2_Definitions.inner_length)))
           (FStar_UInt32.uint_to_t (Prims.of_int (8)))) in
    let s3 = FStar_UInt64.uint_to_t Prims.int_zero in
    let salt_u64 =
      Lib_Sequence.createi (Prims.of_int (2))
        (fun i ->
           let n =
             Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (Obj.magic
                  (Lib_Sequence.sub (Prims.of_int (16))
                     p.Spec_Blake2_Definitions.salt (i * (Prims.of_int (8)))
                     (Prims.of_int (8)))) in
           FStar_UInt64.uint_to_t n) in
    let s4 = Lib_Sequence.index (Prims.of_int (2)) salt_u64 Prims.int_zero in
    let s5 = Lib_Sequence.index (Prims.of_int (2)) salt_u64 Prims.int_one in
    let personal_u64 =
      Lib_Sequence.createi (Prims.of_int (2))
        (fun i ->
           let n =
             Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (Obj.magic
                  (Lib_Sequence.sub (Prims.of_int (16))
                     p.Spec_Blake2_Definitions.personal
                     (i * (Prims.of_int (8))) (Prims.of_int (8)))) in
           FStar_UInt64.uint_to_t n) in
    let s6 =
      Lib_Sequence.index (Prims.of_int (2)) personal_u64 Prims.int_zero in
    let s7 = Lib_Sequence.index (Prims.of_int (2)) personal_u64 Prims.int_one in
    Lib_Sequence.of_list [s0; s1; s2; s3; s4; s5; s6; s7]
let (serialize_blake2_params :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.blake2_params ->
      (Obj.t, unit) Lib_Sequence.lseq)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun a ->
         fun p ->
           match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic (Obj.repr (serialize_blake2s_params p))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic (Obj.repr (serialize_blake2b_params p))) uu___1
        uu___
let (rTable_list_S : (FStar_UInt32.t, unit) FStar_List_Tot_Properties.llist)
  =
  [FStar_UInt32.uint_to_t (Prims.of_int (16));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (7))]
let (rTable_list_B : (FStar_UInt32.t, unit) FStar_List_Tot_Properties.llist)
  =
  [FStar_UInt32.uint_to_t (Prims.of_int (32));
  FStar_UInt32.uint_to_t (Prims.of_int (24));
  FStar_UInt32.uint_to_t (Prims.of_int (16));
  FStar_UInt32.uint_to_t (Prims.of_int (63))]
let (rTable :
  Spec_Blake2_Definitions.alg -> (FStar_UInt32.t, unit) Lib_Sequence.lseq) =
  fun a ->
    match a with
    | Spec_Blake2_Definitions.Blake2S ->
        Lib_Sequence.of_list
          [FStar_UInt32.uint_to_t (Prims.of_int (16));
          FStar_UInt32.uint_to_t (Prims.of_int (12));
          FStar_UInt32.uint_to_t (Prims.of_int (8));
          FStar_UInt32.uint_to_t (Prims.of_int (7))]
    | Spec_Blake2_Definitions.Blake2B ->
        Lib_Sequence.of_list
          [FStar_UInt32.uint_to_t (Prims.of_int (32));
          FStar_UInt32.uint_to_t (Prims.of_int (24));
          FStar_UInt32.uint_to_t (Prims.of_int (16));
          FStar_UInt32.uint_to_t (Prims.of_int (63))]
let (list_iv_S : (FStar_UInt32.t, unit) FStar_List_Tot_Properties.llist) =
  [(Stdint.Uint32.of_string "0x6A09E667");
  (Stdint.Uint32.of_string "0xBB67AE85");
  (Stdint.Uint32.of_string "0x3C6EF372");
  (Stdint.Uint32.of_string "0xA54FF53A");
  (Stdint.Uint32.of_string "0x510E527F");
  (Stdint.Uint32.of_string "0x9B05688C");
  (Stdint.Uint32.of_string "0x1F83D9AB");
  (Stdint.Uint32.of_string "0x5BE0CD19")]
let (list_iv_B : (FStar_UInt64.t, unit) FStar_List_Tot_Properties.llist) =
  [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
  (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
  (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
  (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
  (Stdint.Uint64.of_string "0x510E527FADE682D1");
  (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
  (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
  (Stdint.Uint64.of_string "0x5BE0CD19137E2179")]
let (list_iv :
  Spec_Blake2_Definitions.alg ->
    (Obj.t, unit) FStar_List_Tot_Properties.llist)
  =
  fun uu___ ->
    (fun a ->
       match a with
       | Spec_Blake2_Definitions.Blake2S ->
           Obj.magic
             (Obj.repr
                [(Stdint.Uint32.of_string "0x6A09E667");
                (Stdint.Uint32.of_string "0xBB67AE85");
                (Stdint.Uint32.of_string "0x3C6EF372");
                (Stdint.Uint32.of_string "0xA54FF53A");
                (Stdint.Uint32.of_string "0x510E527F");
                (Stdint.Uint32.of_string "0x9B05688C");
                (Stdint.Uint32.of_string "0x1F83D9AB");
                (Stdint.Uint32.of_string "0x5BE0CD19")])
       | Spec_Blake2_Definitions.Blake2B ->
           Obj.magic
             (Obj.repr
                [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                (Stdint.Uint64.of_string "0x510E527FADE682D1");
                (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])) uu___
let (ivTable :
  Spec_Blake2_Definitions.alg -> (Obj.t, unit) Lib_Sequence.lseq) =
  fun uu___ ->
    (fun a ->
       match a with
       | Spec_Blake2_Definitions.Blake2S ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.of_list
                   [(Stdint.Uint32.of_string "0x6A09E667");
                   (Stdint.Uint32.of_string "0xBB67AE85");
                   (Stdint.Uint32.of_string "0x3C6EF372");
                   (Stdint.Uint32.of_string "0xA54FF53A");
                   (Stdint.Uint32.of_string "0x510E527F");
                   (Stdint.Uint32.of_string "0x9B05688C");
                   (Stdint.Uint32.of_string "0x1F83D9AB");
                   (Stdint.Uint32.of_string "0x5BE0CD19")]))
       | Spec_Blake2_Definitions.Blake2B ->
           Obj.magic
             (Obj.repr
                (Lib_Sequence.of_list
                   [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                   (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                   (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                   (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                   (Stdint.Uint64.of_string "0x510E527FADE682D1");
                   (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                   (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                   (Stdint.Uint64.of_string "0x5BE0CD19137E2179")]))) uu___
let (list_sigma : Spec_Blake2_Definitions.list_sigma_t) =
  [FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t Prims.int_zero;
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (10));
  FStar_UInt32.uint_to_t (Prims.of_int (2));
  FStar_UInt32.uint_to_t (Prims.of_int (8));
  FStar_UInt32.uint_to_t (Prims.of_int (4));
  FStar_UInt32.uint_to_t (Prims.of_int (7));
  FStar_UInt32.uint_to_t (Prims.of_int (6));
  FStar_UInt32.uint_to_t Prims.int_one;
  FStar_UInt32.uint_to_t (Prims.of_int (5));
  FStar_UInt32.uint_to_t (Prims.of_int (15));
  FStar_UInt32.uint_to_t (Prims.of_int (11));
  FStar_UInt32.uint_to_t (Prims.of_int (9));
  FStar_UInt32.uint_to_t (Prims.of_int (14));
  FStar_UInt32.uint_to_t (Prims.of_int (3));
  FStar_UInt32.uint_to_t (Prims.of_int (12));
  FStar_UInt32.uint_to_t (Prims.of_int (13));
  FStar_UInt32.uint_to_t Prims.int_zero]
let (sigmaTable :
  (Spec_Blake2_Definitions.sigma_elt_t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list list_sigma
let (g1 :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      Spec_Blake2_Definitions.row_idx ->
        Spec_Blake2_Definitions.row_idx ->
          FStar_UInt32.t ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      fun i ->
        fun j ->
          fun r ->
            Lib_Sequence.upd (Prims.of_int (4)) wv i
              (Lib_Sequence.map (Prims.of_int (4))
                 (fun u ->
                    Lib_IntTypes.rotate_right
                      (match a with
                       | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                       | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                      Lib_IntTypes.SEC u r)
                 (Lib_Sequence.map2 (Prims.of_int (4))
                    (Lib_IntTypes.logxor
                       (match a with
                        | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                        | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                       Lib_IntTypes.SEC)
                    (Lib_Sequence.index (Prims.of_int (4)) wv i)
                    (Lib_Sequence.index (Prims.of_int (4)) wv j)))
let (g2 :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      Spec_Blake2_Definitions.row_idx ->
        Spec_Blake2_Definitions.row_idx ->
          (Obj.t, unit) Lib_Sequence.lseq ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      fun i ->
        fun j ->
          fun x ->
            Lib_Sequence.upd (Prims.of_int (4)) wv i
              (Lib_Sequence.map2 (Prims.of_int (4))
                 (Lib_IntTypes.add_mod
                    (match a with
                     | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                     | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                    Lib_IntTypes.SEC)
                 (Lib_Sequence.map2 (Prims.of_int (4))
                    (Lib_IntTypes.add_mod
                       (match a with
                        | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                        | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                       Lib_IntTypes.SEC)
                    (Lib_Sequence.index (Prims.of_int (4)) wv i)
                    (Lib_Sequence.index (Prims.of_int (4)) wv j)) x)
let (g2z :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      Spec_Blake2_Definitions.row_idx ->
        Spec_Blake2_Definitions.row_idx ->
          ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      fun i ->
        fun j ->
          Lib_Sequence.upd (Prims.of_int (4)) wv i
            (Lib_Sequence.map2 (Prims.of_int (4))
               (Lib_IntTypes.add_mod
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                  Lib_IntTypes.SEC)
               (Lib_Sequence.index (Prims.of_int (4)) wv i)
               (Lib_Sequence.index (Prims.of_int (4)) wv j))
let (blake2_mixing :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      (Obj.t, unit) Lib_Sequence.lseq ->
        (Obj.t, unit) Lib_Sequence.lseq ->
          ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun al ->
    fun wv ->
      fun x ->
        fun y ->
          let a = Prims.int_zero in
          let b = Prims.int_one in
          let c = (Prims.of_int (2)) in
          let d = (Prims.of_int (3)) in
          let rt =
            match al with
            | Spec_Blake2_Definitions.Blake2S ->
                Lib_Sequence.of_list
                  [FStar_UInt32.uint_to_t (Prims.of_int (16));
                  FStar_UInt32.uint_to_t (Prims.of_int (12));
                  FStar_UInt32.uint_to_t (Prims.of_int (8));
                  FStar_UInt32.uint_to_t (Prims.of_int (7))]
            | Spec_Blake2_Definitions.Blake2B ->
                Lib_Sequence.of_list
                  [FStar_UInt32.uint_to_t (Prims.of_int (32));
                  FStar_UInt32.uint_to_t (Prims.of_int (24));
                  FStar_UInt32.uint_to_t (Prims.of_int (16));
                  FStar_UInt32.uint_to_t (Prims.of_int (63))] in
          let wv1 = g2 al wv a b x in
          let wv2 =
            g1 al wv1 d a
              (Lib_Sequence.index (Prims.of_int (4)) rt Prims.int_zero) in
          let wv3 = g2z al wv2 c d in
          let wv4 =
            g1 al wv3 b c
              (Lib_Sequence.index (Prims.of_int (4)) rt Prims.int_one) in
          let wv5 = g2 al wv4 a b y in
          let wv6 =
            g1 al wv5 d a
              (Lib_Sequence.index (Prims.of_int (4)) rt (Prims.of_int (2))) in
          let wv7 = g2z al wv6 c d in
          let wv8 =
            g1 al wv7 b c
              (Lib_Sequence.index (Prims.of_int (4)) rt (Prims.of_int (3))) in
          wv8
let (diag :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      let wv1 =
        Lib_Sequence.upd (Prims.of_int (4)) wv Prims.int_one
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv Prims.int_one)
                  ((i + Prims.int_one) mod (Prims.of_int (4))))) in
      let wv2 =
        Lib_Sequence.upd (Prims.of_int (4)) wv1 (Prims.of_int (2))
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv1
                     (Prims.of_int (2)))
                  ((i + (Prims.of_int (2))) mod (Prims.of_int (4))))) in
      let wv3 =
        Lib_Sequence.upd (Prims.of_int (4)) wv2 (Prims.of_int (3))
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv2
                     (Prims.of_int (3)))
                  ((i + (Prims.of_int (3))) mod (Prims.of_int (4))))) in
      wv3
let (undiag :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      let wv1 =
        Lib_Sequence.upd (Prims.of_int (4)) wv Prims.int_one
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv Prims.int_one)
                  ((i + (Prims.of_int (3))) mod (Prims.of_int (4))))) in
      let wv2 =
        Lib_Sequence.upd (Prims.of_int (4)) wv1 (Prims.of_int (2))
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv1
                     (Prims.of_int (2)))
                  ((i + (Prims.of_int (2))) mod (Prims.of_int (4))))) in
      let wv3 =
        Lib_Sequence.upd (Prims.of_int (4)) wv2 (Prims.of_int (3))
          (Lib_Sequence.createi (Prims.of_int (4))
             (fun i ->
                Lib_Sequence.index (Prims.of_int (4))
                  (Lib_Sequence.index (Prims.of_int (4)) wv2
                     (Prims.of_int (3)))
                  ((i + Prims.int_one) mod (Prims.of_int (4))))) in
      wv3
let (gather_row :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.block_w ->
      Spec_Blake2_Definitions.sigma_elt_t ->
        Spec_Blake2_Definitions.sigma_elt_t ->
          Spec_Blake2_Definitions.sigma_elt_t ->
            Spec_Blake2_Definitions.sigma_elt_t ->
              (Obj.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun m ->
      fun i0 ->
        fun i1 ->
          fun i2 ->
            fun i3 ->
              Lib_Sequence.of_list
                [Lib_Sequence.index (Prims.of_int (16)) m
                   (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                      (Obj.magic i0));
                Lib_Sequence.index (Prims.of_int (16)) m
                  (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                     (Obj.magic i1));
                Lib_Sequence.index (Prims.of_int (16)) m
                  (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                     (Obj.magic i2));
                Lib_Sequence.index (Prims.of_int (16)) m
                  (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                     (Obj.magic i3))]
let (gather_state :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.block_w ->
      Prims.nat -> ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun m ->
      fun start ->
        let x =
          Lib_Sequence.of_list
            [Lib_Sequence.index (Prims.of_int (16)) m
               (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                  (Obj.magic
                     (Lib_Sequence.index (Prims.of_int (160))
                        (Lib_Sequence.of_list list_sigma) start)));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (2))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (4))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (6))))))] in
        let y =
          Lib_Sequence.of_list
            [Lib_Sequence.index (Prims.of_int (16)) m
               (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                  (Obj.magic
                     (Lib_Sequence.index (Prims.of_int (160))
                        (Lib_Sequence.of_list list_sigma)
                        (start + Prims.int_one))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (3))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (5))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (7))))))] in
        let z =
          Lib_Sequence.of_list
            [Lib_Sequence.index (Prims.of_int (16)) m
               (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                  (Obj.magic
                     (Lib_Sequence.index (Prims.of_int (160))
                        (Lib_Sequence.of_list list_sigma)
                        (start + (Prims.of_int (8))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (10))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (12))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (14))))))] in
        let w =
          Lib_Sequence.of_list
            [Lib_Sequence.index (Prims.of_int (16)) m
               (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                  (Obj.magic
                     (Lib_Sequence.index (Prims.of_int (160))
                        (Lib_Sequence.of_list list_sigma)
                        (start + (Prims.of_int (9))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (11))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (13))))));
            Lib_Sequence.index (Prims.of_int (16)) m
              (Lib_IntTypes.v Lib_IntTypes.U32 Lib_IntTypes.PUB
                 (Obj.magic
                    (Lib_Sequence.index (Prims.of_int (160))
                       (Lib_Sequence.of_list list_sigma)
                       (start + (Prims.of_int (15))))))] in
        let l = [x; y; z; w] in Lib_Sequence.of_list l
let (blake2_round :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.block_w ->
      Prims.nat ->
        ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
          ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun m ->
      fun i ->
        fun wv ->
          let start = (i mod (Prims.of_int (10))) * (Prims.of_int (16)) in
          let m_s = gather_state a m start in
          let wv1 =
            blake2_mixing a wv
              (Lib_Sequence.index (Prims.of_int (4)) m_s Prims.int_zero)
              (Lib_Sequence.index (Prims.of_int (4)) m_s Prims.int_one) in
          let wv2 = diag a wv1 in
          let wv3 =
            blake2_mixing a wv2
              (Lib_Sequence.index (Prims.of_int (4)) m_s (Prims.of_int (2)))
              (Lib_Sequence.index (Prims.of_int (4)) m_s (Prims.of_int (3))) in
          undiag a wv3
let (blake2_compress0 :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.block_s ->
      unit Spec_Blake2_Definitions.block_w)
  =
  fun a ->
    fun m ->
      Lib_Sequence.createi (Prims.of_int (16))
        (fun i ->
           let n =
             Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (Obj.magic
                  (Lib_Sequence.sub
                     ((Prims.of_int (16)) *
                        (Lib_IntTypes.numbytes
                           (match a with
                            | Spec_Blake2_Definitions.Blake2S ->
                                Lib_IntTypes.U32
                            | Spec_Blake2_Definitions.Blake2B ->
                                Lib_IntTypes.U64))) m
                     (i *
                        (Lib_IntTypes.numbytes
                           (match a with
                            | Spec_Blake2_Definitions.Blake2S ->
                                Lib_IntTypes.U32
                            | Spec_Blake2_Definitions.Blake2B ->
                                Lib_IntTypes.U64)))
                     (Lib_IntTypes.numbytes
                        (match a with
                         | Spec_Blake2_Definitions.Blake2S ->
                             Lib_IntTypes.U32
                         | Spec_Blake2_Definitions.Blake2B ->
                             Lib_IntTypes.U64)))) in
           Lib_IntTypes.mk_int
             (match a with
              | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
              | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
             Lib_IntTypes.SEC n)
let (blake2_compress1 :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      Obj.t ->
        Prims.bool ->
          Prims.bool ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun s_iv ->
      fun offset ->
        fun flag ->
          fun last_node_flag ->
            let wv = s_iv in
            let low_offset =
              match match a with
                    | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                    | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64
              with
              | Lib_IntTypes.U32 ->
                  Obj.repr
                    (Lib_IntTypes.to_u32
                       (match match a with
                              | Spec_Blake2_Definitions.Blake2S ->
                                  Lib_IntTypes.U32
                              | Spec_Blake2_Definitions.Blake2B ->
                                  Lib_IntTypes.U64
                        with
                        | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                        | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                       Lib_IntTypes.SEC offset)
              | Lib_IntTypes.U64 ->
                  Obj.repr
                    (Lib_IntTypes.to_u64
                       (match match a with
                              | Spec_Blake2_Definitions.Blake2S ->
                                  Lib_IntTypes.U32
                              | Spec_Blake2_Definitions.Blake2B ->
                                  Lib_IntTypes.U64
                        with
                        | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                        | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                       Lib_IntTypes.SEC offset) in
            let high_offset =
              match match a with
                    | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                    | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64
              with
              | Lib_IntTypes.U32 ->
                  Obj.repr
                    (Lib_IntTypes.to_u32
                       (match match a with
                              | Spec_Blake2_Definitions.Blake2S ->
                                  Lib_IntTypes.U32
                              | Spec_Blake2_Definitions.Blake2B ->
                                  Lib_IntTypes.U64
                        with
                        | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                        | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                       Lib_IntTypes.SEC
                       (Lib_IntTypes.shift_right
                          (match match a with
                                 | Spec_Blake2_Definitions.Blake2S ->
                                     Lib_IntTypes.U32
                                 | Spec_Blake2_Definitions.Blake2B ->
                                     Lib_IntTypes.U64
                           with
                           | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                           | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                          Lib_IntTypes.SEC offset
                          (FStar_UInt32.uint_to_t
                             (Lib_IntTypes.bits
                                (match a with
                                 | Spec_Blake2_Definitions.Blake2S ->
                                     Lib_IntTypes.U32
                                 | Spec_Blake2_Definitions.Blake2B ->
                                     Lib_IntTypes.U64)))))
              | Lib_IntTypes.U64 ->
                  Obj.repr
                    (Lib_IntTypes.to_u64
                       (match match a with
                              | Spec_Blake2_Definitions.Blake2S ->
                                  Lib_IntTypes.U32
                              | Spec_Blake2_Definitions.Blake2B ->
                                  Lib_IntTypes.U64
                        with
                        | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                        | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                       Lib_IntTypes.SEC
                       (Lib_IntTypes.shift_right
                          (match match a with
                                 | Spec_Blake2_Definitions.Blake2S ->
                                     Lib_IntTypes.U32
                                 | Spec_Blake2_Definitions.Blake2B ->
                                     Lib_IntTypes.U64
                           with
                           | Lib_IntTypes.U32 -> Lib_IntTypes.U64
                           | Lib_IntTypes.U64 -> Lib_IntTypes.U128)
                          Lib_IntTypes.SEC offset
                          (FStar_UInt32.uint_to_t
                             (Lib_IntTypes.bits
                                (match a with
                                 | Spec_Blake2_Definitions.Blake2S ->
                                     Lib_IntTypes.U32
                                 | Spec_Blake2_Definitions.Blake2B ->
                                     Lib_IntTypes.U64))))) in
            let m_12 = low_offset in
            let m_13 = high_offset in
            let m_14 =
              if flag
              then
                Lib_IntTypes.ones
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                  Lib_IntTypes.SEC
              else
                (match a with
                 | Spec_Blake2_Definitions.Blake2S ->
                     Obj.repr (FStar_UInt32.uint_to_t Prims.int_zero)
                 | Spec_Blake2_Definitions.Blake2B ->
                     Obj.repr (FStar_UInt64.uint_to_t Prims.int_zero)) in
            let m_15 =
              if last_node_flag
              then
                Lib_IntTypes.ones
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                  Lib_IntTypes.SEC
              else
                (match a with
                 | Spec_Blake2_Definitions.Blake2S ->
                     Obj.repr (FStar_UInt32.uint_to_t Prims.int_zero)
                 | Spec_Blake2_Definitions.Blake2B ->
                     Obj.repr (FStar_UInt64.uint_to_t Prims.int_zero)) in
            let mask = Lib_Sequence.of_list [m_12; m_13; m_14; m_15] in
            let wv1 =
              Lib_Sequence.upd (Prims.of_int (4)) wv (Prims.of_int (3))
                (Lib_Sequence.map2 (Prims.of_int (4))
                   (Lib_IntTypes.logxor
                      (match a with
                       | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                       | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                      Lib_IntTypes.SEC)
                   (Lib_Sequence.index (Prims.of_int (4)) wv
                      (Prims.of_int (3))) mask) in
            wv1
let (blake2_compress2 :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      unit Spec_Blake2_Definitions.block_w ->
        ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      fun m ->
        Lib_LoopCombinators.repeati
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> (Prims.of_int (10))
           | Spec_Blake2_Definitions.Blake2B -> (Prims.of_int (12)))
          (blake2_round a m) wv
let (blake2_compress3 :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
        ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun wv ->
      fun s ->
        let s1 =
          Lib_Sequence.upd (Prims.of_int (4)) s Prims.int_zero
            (Lib_Sequence.map2 (Prims.of_int (4))
               (Lib_IntTypes.logxor
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                  Lib_IntTypes.SEC)
               (Lib_Sequence.map2 (Prims.of_int (4))
                  (Lib_IntTypes.logxor
                     (match a with
                      | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                      | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                     Lib_IntTypes.SEC)
                  (Lib_Sequence.index (Prims.of_int (4)) s Prims.int_zero)
                  (Lib_Sequence.index (Prims.of_int (4)) wv Prims.int_zero))
               (Lib_Sequence.index (Prims.of_int (4)) wv (Prims.of_int (2)))) in
        let s2 =
          Lib_Sequence.upd (Prims.of_int (4)) s1 Prims.int_one
            (Lib_Sequence.map2 (Prims.of_int (4))
               (Lib_IntTypes.logxor
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                  Lib_IntTypes.SEC)
               (Lib_Sequence.map2 (Prims.of_int (4))
                  (Lib_IntTypes.logxor
                     (match a with
                      | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                      | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
                     Lib_IntTypes.SEC)
                  (Lib_Sequence.index (Prims.of_int (4)) s1 Prims.int_one)
                  (Lib_Sequence.index (Prims.of_int (4)) wv Prims.int_one))
               (Lib_Sequence.index (Prims.of_int (4)) wv (Prims.of_int (3)))) in
        s2
let (blake2_compress :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      unit Spec_Blake2_Definitions.block_s ->
        Obj.t ->
          Prims.bool ->
            Prims.bool ->
              ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun s_iv ->
      fun m ->
        fun offset ->
          fun flag ->
            fun last_node_flag ->
              let m_w = blake2_compress0 a m in
              let wv = blake2_compress1 a s_iv offset flag last_node_flag in
              let wv1 = blake2_compress2 a wv m_w in
              let s_iv1 = blake2_compress3 a wv1 s_iv in s_iv1
let (blake2_update_block :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      Prims.bool ->
        Prims.nat ->
          unit Spec_Blake2_Definitions.block_s ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
              ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun flag ->
      fun last_node_flag ->
        fun totlen ->
          fun d ->
            fun s ->
              let offset =
                match match a with
                      | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                      | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64
                with
                | Lib_IntTypes.U32 ->
                    Obj.repr (FStar_UInt64.uint_to_t totlen)
                | Lib_IntTypes.U64 ->
                    Obj.repr
                      (let h =
                         FStar_UInt64.uint_to_t
                           (totlen / (Prims.pow2 (Prims.of_int (64)))) in
                       let l =
                         FStar_UInt64.uint_to_t
                           (totlen mod (Prims.pow2 (Prims.of_int (64)))) in
                       FStar_UInt128.add
                         (FStar_UInt128.shift_left
                            (FStar_UInt128.uint64_to_uint128 h)
                            (Stdint.Uint32.of_int (64)))
                         (FStar_UInt128.uint64_to_uint128 l)) in
              blake2_compress a s d offset flag last_node_flag
let (get_blocki :
  Spec_Blake2_Definitions.alg ->
    FStar_UInt8.t Lib_Sequence.seq ->
      Prims.nat -> unit Spec_Blake2_Definitions.block_s)
  =
  fun a ->
    fun m ->
      fun i ->
        FStar_Seq_Base.slice m
          (i *
             ((Prims.of_int (16)) *
                (Lib_IntTypes.numbytes
                   (match a with
                    | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                    | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))))
          ((i + Prims.int_one) *
             ((Prims.of_int (16)) *
                (Lib_IntTypes.numbytes
                   (match a with
                    | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                    | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))))
let (blake2_update1 :
  Spec_Blake2_Definitions.alg ->
    Prims.nat ->
      FStar_UInt8.t Lib_Sequence.seq ->
        Prims.nat ->
          ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun prev ->
      fun m ->
        fun i ->
          fun s ->
            let totlen =
              prev +
                ((i + Prims.int_one) *
                   ((Prims.of_int (16)) *
                      (Lib_IntTypes.numbytes
                         (match a with
                          | Spec_Blake2_Definitions.Blake2S ->
                              Lib_IntTypes.U32
                          | Spec_Blake2_Definitions.Blake2B ->
                              Lib_IntTypes.U64)))) in
            let d = get_blocki a m i in
            blake2_update_block a false false totlen d s
let (get_last_padded_block :
  Spec_Blake2_Definitions.alg ->
    FStar_UInt8.t Lib_Sequence.seq ->
      Prims.nat -> unit Spec_Blake2_Definitions.block_s)
  =
  fun a ->
    fun m ->
      fun rem ->
        let last =
          FStar_Seq_Base.slice m ((Lib_Sequence.length m) - rem)
            (Lib_Sequence.length m) in
        let last_block =
          Lib_Sequence.create
            ((Prims.of_int (16)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            (FStar_UInt8.uint_to_t Prims.int_zero) in
        let last_block1 =
          Lib_Sequence.update_sub
            ((Prims.of_int (16)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            last_block Prims.int_zero rem last in
        last_block1
let (blake2_update_last :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      Prims.nat ->
        Prims.nat ->
          FStar_UInt8.t Lib_Sequence.seq ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
              ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun last_node_flag ->
      fun prev ->
        fun rem ->
          fun m ->
            fun s ->
              let inlen = Lib_Sequence.length m in
              let totlen = prev + inlen in
              let last_block = get_last_padded_block a m rem in
              blake2_update_block a true last_node_flag totlen last_block s
let (split :
  Spec_Blake2_Definitions.alg -> Prims.nat -> (Prims.nat * Prims.nat)) =
  fun a ->
    fun len ->
      Lib_UpdateMulti.split_at_last_lazy_nb_rem
        ((Prims.of_int (16)) *
           (Lib_IntTypes.numbytes
              (match a with
               | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
               | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))) len
let (blake2_update_blocks :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      Prims.nat ->
        FStar_UInt8.t Lib_Sequence.seq ->
          ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun last_node_flag ->
      fun prev ->
        fun m ->
          fun s ->
            let uu___ = split a (Lib_Sequence.length m) in
            match uu___ with
            | (nb, rem) ->
                let s1 =
                  Lib_LoopCombinators.repeati nb (blake2_update1 a prev m) s in
                blake2_update_last a last_node_flag prev rem m s1
let (blake2_init_hash :
  Spec_Blake2_Definitions.alg ->
    unit Spec_Blake2_Definitions.blake2_params ->
      ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun p ->
      let iv0 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          Prims.int_zero in
      let iv1 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          Prims.int_one in
      let iv2 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (2)) in
      let iv3 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (3)) in
      let iv4 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (4)) in
      let iv5 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (5)) in
      let iv6 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (6)) in
      let iv7 =
        Lib_Sequence.index (Prims.of_int (8))
          (match a with
           | Spec_Blake2_Definitions.Blake2S ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint32.of_string "0x6A09E667");
                       (Stdint.Uint32.of_string "0xBB67AE85");
                       (Stdint.Uint32.of_string "0x3C6EF372");
                       (Stdint.Uint32.of_string "0xA54FF53A");
                       (Stdint.Uint32.of_string "0x510E527F");
                       (Stdint.Uint32.of_string "0x9B05688C");
                       (Stdint.Uint32.of_string "0x1F83D9AB");
                       (Stdint.Uint32.of_string "0x5BE0CD19")]))
           | Spec_Blake2_Definitions.Blake2B ->
               Obj.magic
                 (Obj.repr
                    (Lib_Sequence.of_list
                       [(Stdint.Uint64.of_string "0x6A09E667F3BCC908");
                       (Stdint.Uint64.of_string "0xBB67AE8584CAA73B");
                       (Stdint.Uint64.of_string "0x3C6EF372FE94F82B");
                       (Stdint.Uint64.of_string "0xA54FF53A5F1D36F1");
                       (Stdint.Uint64.of_string "0x510E527FADE682D1");
                       (Stdint.Uint64.of_string "0x9B05688C2B3E6C1F");
                       (Stdint.Uint64.of_string "0x1F83D9ABFB41BD6B");
                       (Stdint.Uint64.of_string "0x5BE0CD19137E2179")])))
          (Prims.of_int (7)) in
      let r0 = Lib_Sequence.of_list [iv0; iv1; iv2; iv3] in
      let r1 = Lib_Sequence.of_list [iv4; iv5; iv6; iv7] in
      let s =
        match a with
        | Spec_Blake2_Definitions.Blake2S ->
            Obj.magic (Obj.repr (serialize_blake2s_params p))
        | Spec_Blake2_Definitions.Blake2B ->
            Obj.magic (Obj.repr (serialize_blake2b_params p)) in
      let iv0' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv0
          (Lib_Sequence.index (Prims.of_int (8)) s Prims.int_zero) in
      let iv1' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv1
          (Lib_Sequence.index (Prims.of_int (8)) s Prims.int_one) in
      let iv2' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv2
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (2))) in
      let iv3' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv3
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (3))) in
      let iv4' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv4
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (4))) in
      let iv5' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv5
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (5))) in
      let iv6' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv6
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (6))) in
      let iv7' =
        Lib_IntTypes.logxor
          (match a with
           | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
           | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)
          Lib_IntTypes.SEC iv7
          (Lib_Sequence.index (Prims.of_int (8)) s (Prims.of_int (7))) in
      let r0' = Lib_Sequence.of_list [iv0'; iv1'; iv2'; iv3'] in
      let r1' = Lib_Sequence.of_list [iv4'; iv5'; iv6'; iv7'] in
      let s_iv = Lib_Sequence.of_list [r0'; r1'; r0; r1] in s_iv
let (blake2_key_block :
  Spec_Blake2_Definitions.alg ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        unit Spec_Blake2_Definitions.block_s)
  =
  fun a ->
    fun kk ->
      fun k ->
        let key_block =
          Lib_Sequence.create
            ((Prims.of_int (16)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            (FStar_UInt8.uint_to_t Prims.int_zero) in
        let key_block1 =
          Lib_Sequence.update_sub
            ((Prims.of_int (16)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            key_block Prims.int_zero kk k in
        key_block1
let (blake2_update_key :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      Prims.nat ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
          Prims.nat ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
              ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun last_node_flag ->
      fun kk ->
        fun k ->
          fun ll ->
            fun s ->
              let key_block = blake2_key_block a kk k in
              if ll = Prims.int_zero
              then
                blake2_update_block a true last_node_flag
                  ((Prims.of_int (16)) *
                     (Lib_IntTypes.numbytes
                        (match a with
                         | Spec_Blake2_Definitions.Blake2S ->
                             Lib_IntTypes.U32
                         | Spec_Blake2_Definitions.Blake2B ->
                             Lib_IntTypes.U64))) key_block s
              else
                blake2_update_block a false false
                  ((Prims.of_int (16)) *
                     (Lib_IntTypes.numbytes
                        (match a with
                         | Spec_Blake2_Definitions.Blake2S ->
                             Lib_IntTypes.U32
                         | Spec_Blake2_Definitions.Blake2B ->
                             Lib_IntTypes.U64))) key_block s
let (blake2_update :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      Prims.nat ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
          FStar_UInt8.t Lib_Sequence.seq ->
            ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
              ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun last_node ->
      fun kk ->
        fun k ->
          fun d ->
            fun s ->
              let ll = Lib_Sequence.length d in
              if kk > Prims.int_zero
              then
                let s1 = blake2_update_key a last_node kk k ll s in
                (if ll = Prims.int_zero
                 then s1
                 else
                   blake2_update_blocks a last_node
                     ((Prims.of_int (16)) *
                        (Lib_IntTypes.numbytes
                           (match a with
                            | Spec_Blake2_Definitions.Blake2S ->
                                Lib_IntTypes.U32
                            | Spec_Blake2_Definitions.Blake2B ->
                                Lib_IntTypes.U64))) d s1)
              else blake2_update_blocks a last_node Prims.int_zero d s
let (blake2_finish :
  Spec_Blake2_Definitions.alg ->
    ((Obj.t, unit) Lib_Sequence.lseq, unit) Lib_Sequence.lseq ->
      Prims.nat -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun s ->
      fun nn ->
        let full =
          Lib_Sequence.op_At_Bar
            ((Prims.of_int (4)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            ((Prims.of_int (4)) *
               (Lib_IntTypes.numbytes
                  (match a with
                   | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                   | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
            (let uu___ =
               Lib_Sequence.generate_blocks
                 (Lib_IntTypes.numbytes
                    (match a with
                     | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                     | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))
                 (Prims.of_int (4)) (Prims.of_int (4)) ()
                 (fun uu___2 ->
                    fun uu___1 ->
                      (Obj.magic
                         (Lib_ByteSequence.uints_to_bytes_le_inner
                            (match a with
                             | Spec_Blake2_Definitions.Blake2S ->
                                 Lib_IntTypes.U32
                             | Spec_Blake2_Definitions.Blake2B ->
                                 Lib_IntTypes.U64) Lib_IntTypes.SEC
                            (Prims.of_int (4))
                            (Lib_Sequence.index (Prims.of_int (4)) s
                               Prims.int_zero))) uu___2 uu___1) (Obj.repr ()) in
             match uu___ with | (uu___1, o) -> o)
            (let uu___ =
               Lib_Sequence.generate_blocks
                 (Lib_IntTypes.numbytes
                    (match a with
                     | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                     | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))
                 (Prims.of_int (4)) (Prims.of_int (4)) ()
                 (fun uu___2 ->
                    fun uu___1 ->
                      (Obj.magic
                         (Lib_ByteSequence.uints_to_bytes_le_inner
                            (match a with
                             | Spec_Blake2_Definitions.Blake2S ->
                                 Lib_IntTypes.U32
                             | Spec_Blake2_Definitions.Blake2B ->
                                 Lib_IntTypes.U64) Lib_IntTypes.SEC
                            (Prims.of_int (4))
                            (Lib_Sequence.index (Prims.of_int (4)) s
                               Prims.int_one))) uu___2 uu___1) (Obj.repr ()) in
             match uu___ with | (uu___1, o) -> o) in
        Lib_Sequence.sub
          (((Prims.of_int (4)) *
              (Lib_IntTypes.numbytes
                 (match a with
                  | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                  | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64)))
             +
             ((Prims.of_int (4)) *
                (Lib_IntTypes.numbytes
                   (match a with
                    | Spec_Blake2_Definitions.Blake2S -> Lib_IntTypes.U32
                    | Spec_Blake2_Definitions.Blake2B -> Lib_IntTypes.U64))))
          full Prims.int_zero nn
let (blake2 :
  Spec_Blake2_Definitions.alg ->
    Prims.bool ->
      FStar_UInt8.t Lib_Sequence.seq ->
        unit Spec_Blake2_Definitions.blake2_params ->
          (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
            (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun last_node ->
      fun d ->
        fun p ->
          fun k ->
            let kk = FStar_UInt8.v p.Spec_Blake2_Definitions.key_length in
            let nn = FStar_UInt8.v p.Spec_Blake2_Definitions.digest_length in
            let s = blake2_init_hash a p in
            let s1 = blake2_update a last_node kk k d s in
            blake2_finish a s1 nn
let (blake2s :
  FStar_UInt8.t Lib_Sequence.seq ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        Prims.nat -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun d ->
    fun kk ->
      fun k ->
        fun n ->
          blake2 Spec_Blake2_Definitions.Blake2S false d
            (let uu___ =
               Spec_Blake2_Definitions.blake2_default_params
                 Spec_Blake2_Definitions.Blake2S in
             {
               Spec_Blake2_Definitions.digest_length =
                 (FStar_UInt8.uint_to_t n);
               Spec_Blake2_Definitions.key_length =
                 (FStar_UInt8.uint_to_t kk);
               Spec_Blake2_Definitions.fanout =
                 (uu___.Spec_Blake2_Definitions.fanout);
               Spec_Blake2_Definitions.depth =
                 (uu___.Spec_Blake2_Definitions.depth);
               Spec_Blake2_Definitions.leaf_length =
                 (uu___.Spec_Blake2_Definitions.leaf_length);
               Spec_Blake2_Definitions.node_offset =
                 (uu___.Spec_Blake2_Definitions.node_offset);
               Spec_Blake2_Definitions.node_depth =
                 (uu___.Spec_Blake2_Definitions.node_depth);
               Spec_Blake2_Definitions.inner_length =
                 (uu___.Spec_Blake2_Definitions.inner_length);
               Spec_Blake2_Definitions.salt =
                 (uu___.Spec_Blake2_Definitions.salt);
               Spec_Blake2_Definitions.personal =
                 (uu___.Spec_Blake2_Definitions.personal)
             }) k
let (blake2b :
  FStar_UInt8.t Lib_Sequence.seq ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        Prims.nat -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun d ->
    fun kk ->
      fun k ->
        fun n ->
          blake2 Spec_Blake2_Definitions.Blake2B false d
            (let uu___ =
               Spec_Blake2_Definitions.blake2_default_params
                 Spec_Blake2_Definitions.Blake2B in
             {
               Spec_Blake2_Definitions.digest_length =
                 (FStar_UInt8.uint_to_t n);
               Spec_Blake2_Definitions.key_length =
                 (FStar_UInt8.uint_to_t kk);
               Spec_Blake2_Definitions.fanout =
                 (uu___.Spec_Blake2_Definitions.fanout);
               Spec_Blake2_Definitions.depth =
                 (uu___.Spec_Blake2_Definitions.depth);
               Spec_Blake2_Definitions.leaf_length =
                 (uu___.Spec_Blake2_Definitions.leaf_length);
               Spec_Blake2_Definitions.node_offset =
                 (uu___.Spec_Blake2_Definitions.node_offset);
               Spec_Blake2_Definitions.node_depth =
                 (uu___.Spec_Blake2_Definitions.node_depth);
               Spec_Blake2_Definitions.inner_length =
                 (uu___.Spec_Blake2_Definitions.inner_length);
               Spec_Blake2_Definitions.salt =
                 (uu___.Spec_Blake2_Definitions.salt);
               Spec_Blake2_Definitions.personal =
                 (uu___.Spec_Blake2_Definitions.personal)
             }) k