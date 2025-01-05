open Prims
let (mk_p256_comm_monoid :
  Spec_P256_PointOps.aff_point Lib_Exponentiation_Definition.comm_monoid) =
  {
    Lib_Exponentiation_Definition.one = Spec_P256_PointOps.aff_point_at_inf;
    Lib_Exponentiation_Definition.mul = Spec_P256_PointOps.aff_point_add;
    Lib_Exponentiation_Definition.lemma_one = ();
    Lib_Exponentiation_Definition.lemma_mul_assoc = ();
    Lib_Exponentiation_Definition.lemma_mul_comm = ()
  }
let (mk_to_p256_comm_monoid :
  Spec_P256_PointOps.proj_point Spec_Exponentiation.to_comm_monoid) =
  {
    Spec_Exponentiation.a_spec = ();
    Spec_Exponentiation.comm_monoid = (Obj.magic mk_p256_comm_monoid);
    Spec_Exponentiation.refl =
      (fun uu___ -> (Obj.magic Spec_P256_PointOps.to_aff_point) uu___)
  }
let (point_at_inf_c : unit -> Spec_P256_PointOps.proj_point) =
  fun uu___ -> Spec_P256_PointOps.point_at_inf
let (point_add_c :
  Spec_P256_PointOps.proj_point ->
    Spec_P256_PointOps.proj_point -> Spec_P256_PointOps.proj_point)
  = fun p -> fun q -> Spec_P256_PointOps.point_add p q
let (point_double_c :
  Spec_P256_PointOps.proj_point -> Spec_P256_PointOps.proj_point) =
  fun p -> Spec_P256_PointOps.point_double p
let (mk_p256_concrete_ops :
  Spec_P256_PointOps.proj_point Spec_Exponentiation.concrete_ops) =
  {
    Spec_Exponentiation.to1 = mk_to_p256_comm_monoid;
    Spec_Exponentiation.one = point_at_inf_c;
    Spec_Exponentiation.mul = point_add_c;
    Spec_Exponentiation.sqr = point_double_c
  }
let (point_mul :
  Spec_P256_PointOps.qelem ->
    Spec_P256_PointOps.proj_point -> Spec_P256_PointOps.proj_point)
  =
  fun a ->
    fun p ->
      Spec_Exponentiation.exp_fw mk_p256_concrete_ops p (Prims.of_int (256))
        a (Prims.of_int (4))
let (point_mul_g : Spec_P256_PointOps.qelem -> Spec_P256_PointOps.proj_point)
  = fun a -> point_mul a Spec_P256_PointOps.base_point
let (point_mul_double_g :
  Spec_P256_PointOps.qelem ->
    Spec_P256_PointOps.qelem ->
      Spec_P256_PointOps.proj_point -> Spec_P256_PointOps.proj_point)
  =
  fun a1 ->
    fun a2 ->
      fun p ->
        Spec_Exponentiation.exp_double_fw mk_p256_concrete_ops
          Spec_P256_PointOps.base_point (Prims.of_int (256)) a1 p a2
          (Prims.of_int (5))
type hash_alg_ecdsa =
  | NoHash 
  | Hash of Spec_Hash_Definitions.hash_alg 
let (uu___is_NoHash : hash_alg_ecdsa -> Prims.bool) =
  fun projectee -> match projectee with | NoHash -> true | uu___ -> false
let (uu___is_Hash : hash_alg_ecdsa -> Prims.bool) =
  fun projectee -> match projectee with | Hash _0 -> true | uu___ -> false
let (__proj__Hash__item___0 :
  hash_alg_ecdsa -> Spec_Hash_Definitions.hash_alg) =
  fun projectee -> match projectee with | Hash _0 -> _0
let (min_input_length : hash_alg_ecdsa -> Prims.nat) =
  fun a ->
    match a with | NoHash -> (Prims.of_int (32)) | Hash a1 -> Prims.int_zero
let (hash_ecdsa :
  hash_alg_ecdsa ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun msg_len ->
      fun msg ->
        match a with
        | NoHash -> msg
        | Hash a1 -> Spec_Agile_Hash.hash' a1 msg (Obj.repr ())
let (ecdsa_sign_msg_as_qelem :
  Spec_P256_PointOps.qelem ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq
          FStar_Pervasives_Native.option)
  =
  fun m ->
    fun private_key ->
      fun nonce ->
        let k_q =
          Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
            Lib_IntTypes.SEC (Obj.magic nonce) in
        let d_a =
          Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
            Lib_IntTypes.SEC (Obj.magic private_key) in
        let is_privkey_valid =
          (Prims.int_zero < d_a) && (d_a < Spec_P256_PointOps.order) in
        let is_nonce_valid =
          (Prims.int_zero < k_q) && (k_q < Spec_P256_PointOps.order) in
        if Prims.op_Negation (is_privkey_valid && is_nonce_valid)
        then FStar_Pervasives_Native.None
        else
          (let uu___1 = point_mul_g k_q in
           match uu___1 with
           | (_X, _Y, _Z) ->
               let x = Spec_P256_PointOps.op_Slash_Percent _X _Z in
               let r = x mod Spec_P256_PointOps.order in
               let kinv = Spec_P256_PointOps.qinv k_q in
               let s =
                 Spec_P256_PointOps.op_Star_Hat kinv
                   (Spec_P256_PointOps.op_Plus_Hat m
                      (Spec_P256_PointOps.op_Star_Hat r d_a)) in
               let rb =
                 Obj.magic
                   (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
                      Lib_IntTypes.SEC (Prims.of_int (32)) r) in
               let sb =
                 Obj.magic
                   (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
                      Lib_IntTypes.SEC (Prims.of_int (32)) s) in
               if (r = Prims.int_zero) || (s = Prims.int_zero)
               then FStar_Pervasives_Native.None
               else
                 FStar_Pervasives_Native.Some
                   (Lib_Sequence.concat (Prims.of_int (32))
                      (Prims.of_int (32)) rb sb))
let (ecdsa_verify_msg_as_qelem :
  Spec_P256_PointOps.qelem ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq -> Prims.bool)
  =
  fun m ->
    fun public_key ->
      fun sign_r ->
        fun sign_s ->
          let pk = Spec_P256_PointOps.load_point public_key in
          let r =
            Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
              Lib_IntTypes.SEC (Obj.magic sign_r) in
          let s =
            Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
              Lib_IntTypes.SEC (Obj.magic sign_s) in
          let is_r_valid =
            (Prims.int_zero < r) && (r < Spec_P256_PointOps.order) in
          let is_s_valid =
            (Prims.int_zero < s) && (s < Spec_P256_PointOps.order) in
          if
            Prims.op_Negation
              (((FStar_Pervasives_Native.uu___is_Some pk) && is_r_valid) &&
                 is_s_valid)
          then false
          else
            (let sinv = Spec_P256_PointOps.qinv s in
             let u1 = Spec_P256_PointOps.op_Star_Hat sinv m in
             let u2 = Spec_P256_PointOps.op_Star_Hat sinv r in
             let uu___1 =
               point_mul_double_g u1 u2
                 (FStar_Pervasives_Native.__proj__Some__item__v pk) in
             match uu___1 with
             | (_X, _Y, _Z) ->
                 if Spec_P256_PointOps.is_point_at_inf (_X, _Y, _Z)
                 then false
                 else
                   (let x = Spec_P256_PointOps.op_Slash_Percent _X _Z in
                    (x mod Spec_P256_PointOps.order) = r))
let (ecdsa_signature_agile :
  hash_alg_ecdsa ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
          (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
            (FStar_UInt8.t, unit) Lib_Sequence.lseq
              FStar_Pervasives_Native.option)
  =
  fun alg ->
    fun msg_len ->
      fun msg ->
        fun private_key ->
          fun nonce ->
            let hashM = hash_ecdsa alg msg_len msg in
            let m_q =
              (Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
                 Lib_IntTypes.SEC
                 (Obj.magic
                    (Lib_Sequence.sub
                       (if uu___is_Hash alg
                        then
                          Spec_Hash_Definitions.hash_length
                            (match alg with | Hash a -> a)
                        else msg_len) hashM Prims.int_zero
                       (Prims.of_int (32)))))
                mod Spec_P256_PointOps.order in
            ecdsa_sign_msg_as_qelem m_q private_key nonce
let (ecdsa_verification_agile :
  hash_alg_ecdsa ->
    Prims.nat ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
          (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
            (FStar_UInt8.t, unit) Lib_Sequence.lseq -> Prims.bool)
  =
  fun alg ->
    fun msg_len ->
      fun msg ->
        fun public_key ->
          fun signature_r ->
            fun signature_s ->
              let hashM = hash_ecdsa alg msg_len msg in
              let m_q =
                (Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
                   Lib_IntTypes.SEC
                   (Obj.magic
                      (Lib_Sequence.sub
                         (if uu___is_Hash alg
                          then
                            Spec_Hash_Definitions.hash_length
                              (match alg with | Hash a -> a)
                          else msg_len) hashM Prims.int_zero
                         (Prims.of_int (32)))))
                  mod Spec_P256_PointOps.order in
              ecdsa_verify_msg_as_qelem m_q public_key signature_r
                signature_s
let (secret_to_public :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq FStar_Pervasives_Native.option)
  =
  fun private_key ->
    let sk =
      Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8 Lib_IntTypes.SEC
        (Obj.magic private_key) in
    let is_sk_valid =
      (Prims.int_zero < sk) && (sk < Spec_P256_PointOps.order) in
    if is_sk_valid
    then
      let pk = point_mul_g sk in
      FStar_Pervasives_Native.Some (Spec_P256_PointOps.point_store pk)
    else FStar_Pervasives_Native.None
let (ecdh :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq FStar_Pervasives_Native.option)
  =
  fun their_public_key ->
    fun private_key ->
      let pk = Spec_P256_PointOps.load_point their_public_key in
      let sk =
        Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8 Lib_IntTypes.SEC
          (Obj.magic private_key) in
      let is_sk_valid =
        (Prims.int_zero < sk) && (sk < Spec_P256_PointOps.order) in
      if (FStar_Pervasives_Native.uu___is_Some pk) && is_sk_valid
      then
        let ss =
          point_mul sk (FStar_Pervasives_Native.__proj__Some__item__v pk) in
        FStar_Pervasives_Native.Some (Spec_P256_PointOps.point_store ss)
      else FStar_Pervasives_Native.None
let (validate_public_key :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq -> Prims.bool) =
  fun pk ->
    FStar_Pervasives_Native.uu___is_Some (Spec_P256_PointOps.load_point pk)
let (pk_uncompressed_to_raw :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq FStar_Pervasives_Native.option)
  =
  fun pk ->
    if (Lib_Sequence.index (Prims.of_int (65)) pk Prims.int_zero) <> 0x04
    then FStar_Pervasives_Native.None
    else
      FStar_Pervasives_Native.Some
        (Lib_Sequence.sub (Prims.of_int (65)) pk Prims.int_one
           (Prims.of_int (64)))
let (pk_uncompressed_from_raw :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun pk ->
    Lib_Sequence.concat Prims.int_one (Prims.of_int (64))
      (Lib_Sequence.create Prims.int_one
         (FStar_UInt8.uint_to_t (Prims.of_int (0x04)))) pk
let (pk_compressed_to_raw :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq FStar_Pervasives_Native.option)
  =
  fun pk ->
    let pk_x =
      Lib_Sequence.sub (Prims.of_int (33)) pk Prims.int_one
        (Prims.of_int (32)) in
    match Spec_P256_PointOps.aff_point_decompress pk with
    | FStar_Pervasives_Native.Some (x, y) ->
        FStar_Pervasives_Native.Some
          (Lib_Sequence.concat (Prims.of_int (32)) (Prims.of_int (32)) pk_x
             (Obj.magic
                (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
                   Lib_IntTypes.SEC (Prims.of_int (32)) y)))
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (pk_compressed_from_raw :
  (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun pk ->
    let pk_x =
      Lib_Sequence.sub (Prims.of_int (64)) pk Prims.int_zero
        (Prims.of_int (32)) in
    let pk_y =
      Lib_Sequence.sub (Prims.of_int (64)) pk (Prims.of_int (32))
        (Prims.of_int (32)) in
    let is_pk_y_odd =
      ((Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8 Lib_IntTypes.SEC
          (Obj.magic pk_y))
         mod (Prims.of_int (2)))
        = Prims.int_one in
    let pk0 =
      if is_pk_y_odd
      then FStar_UInt8.uint_to_t (Prims.of_int (0x03))
      else FStar_UInt8.uint_to_t (Prims.of_int (0x02)) in
    Lib_Sequence.concat Prims.int_one (Prims.of_int (32))
      (Lib_Sequence.create Prims.int_one pk0) pk_x