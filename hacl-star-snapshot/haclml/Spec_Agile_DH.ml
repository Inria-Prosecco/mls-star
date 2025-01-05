open Prims
type algorithm =
  | DH_Curve25519 
  | DH_P256 
let (uu___is_DH_Curve25519 : algorithm -> Prims.bool) =
  fun projectee ->
    match projectee with | DH_Curve25519 -> true | uu___ -> false
let (uu___is_DH_P256 : algorithm -> Prims.bool) =
  fun projectee -> match projectee with | DH_P256 -> true | uu___ -> false
let (size_key : algorithm -> Prims.nat) =
  fun a ->
    match a with
    | DH_Curve25519 -> (Prims.of_int (32))
    | DH_P256 -> (Prims.of_int (32))
let (size_public : algorithm -> Prims.nat) =
  fun a ->
    match a with
    | DH_Curve25519 -> (Prims.of_int (32))
    | DH_P256 -> (Prims.of_int (64))
let (prime : algorithm -> Prims.pos) =
  fun a ->
    match a with
    | DH_Curve25519 -> Spec_Curve25519.prime
    | DH_P256 -> Spec_P256_PointOps.prime
type 'a scalar = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'a serialized_point = (FStar_UInt8.t, unit) Lib_Sequence.lseq
let (clamp : algorithm -> unit scalar -> unit scalar) =
  fun a ->
    fun k -> match a with | DH_Curve25519 -> Spec_Curve25519.decodeScalar k
let (dh :
  algorithm ->
    unit scalar ->
      unit serialized_point ->
        unit serialized_point FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      fun p ->
        match a with
        | DH_Curve25519 ->
            let output = Spec_Curve25519.scalarmult s p in
            let is_valid =
              Prims.op_Negation
                (let res =
                   Obj.magic
                     (Lib_ByteSequence.seq_eq_mask Lib_IntTypes.U8
                        (match a with
                         | DH_Curve25519 -> (Prims.of_int (32))
                         | DH_P256 -> (Prims.of_int (64)))
                        (match a with
                         | DH_Curve25519 -> (Prims.of_int (32))
                         | DH_P256 -> (Prims.of_int (64)))
                        (Obj.magic
                           (Lib_Sequence.create
                              (match a with
                               | DH_Curve25519 -> (Prims.of_int (32))
                               | DH_P256 -> (Prims.of_int (64)))
                              (FStar_UInt8.uint_to_t Prims.int_zero)))
                        (Obj.magic output)
                        (match a with
                         | DH_Curve25519 -> (Prims.of_int (32))
                         | DH_P256 -> (Prims.of_int (64)))) in
                 res = 255) in
            if is_valid
            then FStar_Pervasives_Native.Some output
            else FStar_Pervasives_Native.None
        | DH_P256 -> Spec_P256.ecdh p s
let (secret_to_public :
  algorithm ->
    unit scalar -> unit serialized_point FStar_Pervasives_Native.option)
  =
  fun a ->
    fun kpriv ->
      match a with
      | DH_Curve25519 ->
          FStar_Pervasives_Native.Some
            (Spec_Curve25519.secret_to_public kpriv)
      | DH_P256 -> Spec_P256.secret_to_public kpriv