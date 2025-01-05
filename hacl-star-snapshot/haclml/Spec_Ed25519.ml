open Prims
let (size_signature : Prims.nat) = (Prims.of_int (64))
let (q : Prims.nat) =
  (Prims.pow2 (Prims.of_int (252))) +
    (Prims.parse_int "27742317777372353535851937790883648493")
let (max_input_length_sha512 : Prims.pos) =
  FStar_Pervasives_Native.__proj__Some__item__v
    (FStar_Pervasives_Native.Some
       ((Prims.pow2 (Prims.of_int (125))) - Prims.int_one))
let (sha512_modq : Prims.nat -> FStar_UInt8.t Lib_Sequence.seq -> Prims.nat)
  =
  fun len ->
    fun s ->
      (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8 Lib_IntTypes.SEC
         (Obj.magic
            (Spec_Agile_Hash.hash' Spec_Hash_Definitions.SHA2_512 s
               (Obj.repr ()))))
        mod q
type aff_point_c = Spec_Ed25519_PointOps.aff_point
let (aff_point_add_c : aff_point_c -> aff_point_c -> aff_point_c) =
  fun p -> fun q1 -> Spec_Ed25519_PointOps.aff_point_add p q1
let (mk_ed25519_comm_monoid :
  aff_point_c Lib_Exponentiation_Definition.comm_monoid) =
  {
    Lib_Exponentiation_Definition.one =
      Spec_Ed25519_PointOps.aff_point_at_infinity;
    Lib_Exponentiation_Definition.mul = aff_point_add_c;
    Lib_Exponentiation_Definition.lemma_one = ();
    Lib_Exponentiation_Definition.lemma_mul_assoc = ();
    Lib_Exponentiation_Definition.lemma_mul_comm = ()
  }
type ext_point_c = Spec_Ed25519_PointOps.ext_point
let (mk_to_ed25519_comm_monoid :
  ext_point_c Spec_Exponentiation.to_comm_monoid) =
  {
    Spec_Exponentiation.a_spec = ();
    Spec_Exponentiation.comm_monoid = (Obj.magic mk_ed25519_comm_monoid);
    Spec_Exponentiation.refl =
      (fun uu___ ->
         (fun x -> Obj.magic (Spec_Ed25519_PointOps.to_aff_point x)) uu___)
  }
let (point_at_inifinity_c : unit -> ext_point_c) =
  fun uu___ -> Spec_Ed25519_PointOps.point_at_infinity
let (point_add_c : ext_point_c -> ext_point_c -> ext_point_c) =
  fun p -> fun q1 -> Spec_Ed25519_PointOps.point_add p q1
let (point_double_c : ext_point_c -> ext_point_c) =
  fun p -> Spec_Ed25519_PointOps.point_double p
let (mk_ed25519_concrete_ops : ext_point_c Spec_Exponentiation.concrete_ops)
  =
  {
    Spec_Exponentiation.to1 = mk_to_ed25519_comm_monoid;
    Spec_Exponentiation.one = point_at_inifinity_c;
    Spec_Exponentiation.mul = point_add_c;
    Spec_Exponentiation.sqr = point_double_c
  }
let (point_mul :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq -> ext_point_c -> ext_point_c) =
  fun a ->
    fun p ->
      Spec_Exponentiation.exp_fw mk_ed25519_concrete_ops p
        (Prims.of_int (256))
        (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
           Lib_IntTypes.SEC (Obj.magic a)) (Prims.of_int (4))
let (point_mul_double :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    ext_point_c ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq -> ext_point_c -> ext_point_c)
  =
  fun a1 ->
    fun p1 ->
      fun a2 ->
        fun p2 ->
          Spec_Exponentiation.exp_double_fw mk_ed25519_concrete_ops p1
            (Prims.of_int (256))
            (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC (Obj.magic a1)) p2
            (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
               Lib_IntTypes.SEC (Obj.magic a2)) (Prims.of_int (5))
let (point_mul_g : (FStar_UInt8.t, unit) Lib_Sequence.lseq -> ext_point_c) =
  fun a -> point_mul a Spec_Ed25519_PointOps.g
let (point_mul_double_g :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq -> ext_point_c -> ext_point_c)
  =
  fun a1 ->
    fun a2 -> fun p -> point_mul_double a1 Spec_Ed25519_PointOps.g a2 p
let (point_negate_mul_double_g :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq -> ext_point_c -> ext_point_c)
  =
  fun a1 ->
    fun a2 ->
      fun p ->
        let p1 = Spec_Ed25519_PointOps.point_negate p in
        point_mul_double_g a1 a2 p1
let (secret_expand :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    ((FStar_UInt8.t, unit) Lib_Sequence.lseq * (FStar_UInt8.t, unit)
      Lib_Sequence.lseq))
  =
  fun secret ->
    let h =
      Spec_Agile_Hash.hash' Spec_Hash_Definitions.SHA2_512 secret
        (Obj.repr ()) in
    let h_low =
      Lib_Sequence.slice
        (Spec_Hash_Definitions.hash_length' Spec_Hash_Definitions.SHA2_512
           (Obj.repr ())) h Prims.int_zero (Prims.of_int (32)) in
    let h_high =
      Lib_Sequence.slice
        (Spec_Hash_Definitions.hash_length' Spec_Hash_Definitions.SHA2_512
           (Obj.repr ())) h (Prims.of_int (32)) (Prims.of_int (64)) in
    let h_low1 =
      Lib_Sequence.upd (Prims.of_int (32)) h_low Prims.int_zero
        (FStar_UInt8.logand
           (Lib_Sequence.index (Prims.of_int (32)) h_low Prims.int_zero)
           (FStar_UInt8.uint_to_t (Prims.of_int (0xf8)))) in
    let h_low2 =
      Lib_Sequence.upd (Prims.of_int (32)) h_low1 (Prims.of_int (31))
        (FStar_UInt8.logor
           (FStar_UInt8.logand
              (Lib_Sequence.index (Prims.of_int (32)) h_low1
                 (Prims.of_int (31)))
              (FStar_UInt8.uint_to_t (Prims.of_int (127))))
           (FStar_UInt8.uint_to_t (Prims.of_int (64)))) in
    (h_low2, h_high)
let (secret_to_public :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun secret ->
    let uu___ = secret_expand secret in
    match uu___ with
    | (a, dummy) -> Spec_Ed25519_PointOps.point_compress (point_mul_g a)
let (expand_keys :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    ((FStar_UInt8.t, unit) Lib_Sequence.lseq * (FStar_UInt8.t, unit)
      Lib_Sequence.lseq * (FStar_UInt8.t, unit) Lib_Sequence.lseq))
  =
  fun secret ->
    let uu___ = secret_expand secret in
    match uu___ with
    | (s, prefix) ->
        let pub = Spec_Ed25519_PointOps.point_compress (point_mul_g s) in
        (pub, s, prefix)
let (sign_expanded :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        FStar_UInt8.t Lib_Sequence.seq ->
          (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun pub ->
    fun s ->
      fun prefix ->
        fun msg ->
          let len = Lib_Sequence.length msg in
          let r =
            sha512_modq ((Prims.of_int (32)) + len)
              (FStar_Seq_Base.append prefix msg) in
          let r' =
            point_mul_g
              (Obj.magic
                 (Lib_ByteSequence.nat_to_intseq_le_ Lib_IntTypes.U8
                    Lib_IntTypes.SEC (Prims.of_int (32)) r)) in
          let rs = Spec_Ed25519_PointOps.point_compress r' in
          let h =
            sha512_modq ((Prims.of_int (64)) + len)
              (FStar_Seq_Base.append
                 (Lib_Sequence.concat (Prims.of_int (32)) (Prims.of_int (32))
                    rs pub) msg) in
          let s1 =
            (r +
               ((h *
                   (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
                      Lib_IntTypes.SEC (Obj.magic s)))
                  mod q))
              mod q in
          Lib_Sequence.concat (Prims.of_int (32)) (Prims.of_int (32)) rs
            (Obj.magic
               (Lib_ByteSequence.nat_to_intseq_le_ Lib_IntTypes.U8
                  Lib_IntTypes.SEC (Prims.of_int (32)) s1))
let (sign :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    FStar_UInt8.t Lib_Sequence.seq -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun secret ->
    fun msg ->
      let uu___ = expand_keys secret in
      match uu___ with | (pub, s, prefix) -> sign_expanded pub s prefix msg
let (verify :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    FStar_UInt8.t Lib_Sequence.seq ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq -> Prims.bool)
  =
  fun public ->
    fun msg ->
      fun signature ->
        let len = Lib_Sequence.length msg in
        let a' = Spec_Ed25519_PointOps.point_decompress public in
        match a' with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some a'1 ->
            let rs =
              Lib_Sequence.slice (Prims.of_int (64)) signature Prims.int_zero
                (Prims.of_int (32)) in
            let r' = Spec_Ed25519_PointOps.point_decompress rs in
            (match r' with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some r'1 ->
                 let sb =
                   Lib_Sequence.slice (Prims.of_int (64)) signature
                     (Prims.of_int (32)) (Prims.of_int (64)) in
                 if
                   (Lib_ByteSequence.nat_from_intseq_le_ Lib_IntTypes.U8
                      Lib_IntTypes.SEC (Obj.magic sb))
                     >= q
                 then false
                 else
                   (let h =
                      sha512_modq ((Prims.of_int (64)) + len)
                        (FStar_Seq_Base.append
                           (Lib_Sequence.concat (Prims.of_int (32))
                              (Prims.of_int (32)) rs public) msg) in
                    let hb =
                      Obj.magic
                        (Lib_ByteSequence.nat_to_intseq_le_ Lib_IntTypes.U8
                           Lib_IntTypes.SEC (Prims.of_int (32)) h) in
                    let exp_d = point_negate_mul_double_g sb hb a'1 in
                    Spec_Ed25519_PointOps.point_equal exp_d r'1))