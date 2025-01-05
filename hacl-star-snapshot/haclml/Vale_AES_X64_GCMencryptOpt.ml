open Prims
type ('alg, 'key, 'roundukeys, 'keysub, 'keyuptr, 'heap0, 'layout) aes_reqs =
  unit
let (va_code_Gctr_register :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (9));
      Vale_AES_X64_AES.va_code_AESEncryptBlock alg;
      Vale_X64_Machine_s.Block [];
      Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (8)) (Prims.of_int (9));
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (8)) Prims.int_zero]
let (va_codegen_success_Gctr_register :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
         (Prims.of_int (9)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_AES_X64_AES.va_codegen_success_AESEncryptBlock alg)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Pshufb (Prims.of_int (8))
               (Prims.of_int (9)))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Pxor (Prims.of_int (8))
                  Prims.int_zero) (Vale_X64_Decls.va_ttrue ()))))

type ('alg, 'key, 'roundukeys, 'keysub, 'vaus0, 'vauk) va_wp_Gctr_register =
  unit

let (va_code_Gctr_blocks128_body0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Mov128 Prims.int_zero (Prims.of_int (11));
      Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (9));
      Vale_AES_X64_AES.va_code_AESEncryptBlock alg;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_one
        (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (2)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (2))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsBasic.va_code_Add64 (Vale_X64_Machine_s.OReg Prims.int_one)
        (Vale_X64_Machine_s.OConst Prims.int_one);
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      Vale_AES_X64_GCTR.va_code_Inc32 (Prims.of_int (11)) (Prims.of_int (10))]
let (va_codegen_success_Gctr_blocks128_body0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Mov128 Prims.int_zero
         (Prims.of_int (11)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
            (Prims.of_int (9)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_AES_X64_AES.va_codegen_success_AESEncryptBlock alg)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                  Prims.int_one (Prims.of_int (2))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                  Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Pxor
                     (Prims.of_int (2)) Prims.int_zero)
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                        Prims.int_one
                        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                        (Prims.of_int (2)) Prims.int_zero
                        Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_Add64
                           (Vale_X64_Machine_s.OReg Prims.int_one)
                           (Vale_X64_Machine_s.OConst Prims.int_one))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsBasic.va_codegen_success_Add64
                              (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                              (Vale_X64_Machine_s.OConst (Prims.of_int (16))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_Add64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                                 (Vale_X64_Machine_s.OConst
                                    (Prims.of_int (16))))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_AES_X64_GCTR.va_codegen_success_Inc32
                                    (Prims.of_int (11)) (Prims.of_int (10)))
                                 (Vale_X64_Decls.va_ttrue ()))))))))))

type ('vauold, 'alg, 'vauinuinub, 'vauinukey, 'vauinukeysub, 'vauinuoutub,
  'vauinuplainuquads, 'vauinuroundukeys, 'vaus0,
  'vauk) va_wp_Gctr_blocks128_body0 = unit

let (va_code_Gctr_blocks128_while0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.While
         ((Vale_X64_Decls.va_cmp_ne (Vale_X64_Machine_s.OReg Prims.int_one)
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))),
           (Vale_X64_Machine_s.Block [va_code_Gctr_blocks128_body0 alg]))]
let (va_codegen_success_Gctr_blocks128_while0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Gctr_blocks128_body0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinuinub, 'vauinukey, 'vauinukeysub, 'vauinuoutub,
  'vauinuplainuquads, 'vauinuroundukeys, 'vaus0,
  'vauk) va_wp_Gctr_blocks128_while0 = unit

let (va_code_Gctr_blocks128 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (10));
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (10)) Prims.int_one
        Prims.int_zero (Vale_X64_Machine_s.OReg Prims.int_one);
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
      Vale_X64_InsBasic.va_code_Mov64 (Vale_X64_Machine_s.OReg Prims.int_one)
        (Vale_X64_Machine_s.OConst Prims.int_zero);
      va_code_Gctr_blocks128_while0 alg]
let (va_codegen_success_Gctr_blocks128 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_ZeroXmm (Prims.of_int (10)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_PinsrdImm (Prims.of_int (10))
            Prims.int_one Prims.int_zero
            (Vale_X64_Machine_s.OReg Prims.int_one))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
               (Vale_X64_Machine_s.OReg Prims.int_zero))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsBasic.va_codegen_success_Mov64
                  (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Mov64
                     (Vale_X64_Machine_s.OReg Prims.int_one)
                     (Vale_X64_Machine_s.OConst Prims.int_zero))
                  (Vale_X64_Decls.va_pbool_and
                     (va_codegen_success_Gctr_blocks128_while0 alg)
                     (Vale_X64_Decls.va_ttrue ()))))))

type ('alg, 'inub, 'outub, 'key, 'roundukeys, 'keysub, 'vaus0,
  'vauk) va_wp_Gctr_blocks128 = unit

let (va_code_Gcm_blocks128 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [va_code_Gctr_blocks128 alg;
      Vale_AES_X64_AESopt2.va_code_Ghash_buffer ()]
let (va_codegen_success_Gcm_blocks128 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Gctr_blocks128 alg)
      (Vale_X64_Decls.va_pbool_and
         (Vale_AES_X64_AESopt2.va_codegen_success_Ghash_buffer ())
         (Vale_X64_Decls.va_ttrue ()))

type ('alg, 'inub, 'outub, 'key, 'roundukeys, 'keysub, 'hkeysub, 'huLE,
  'vaus0, 'vauk) va_wp_Gcm_blocks128 = unit

let (va_code_Gcm_auth_bytes :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (8));
      Vale_AES_X64_AESopt2.va_code_Ghash_buffer ()]
let (va_codegen_success_Gcm_auth_bytes : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_ZeroXmm (Prims.of_int (8)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_AES_X64_AESopt2.va_codegen_success_Ghash_buffer ())
         (Vale_X64_Decls.va_ttrue ()))

type ('authub, 'hkeysub, 'huLE, 'vaus0, 'vauk) va_wp_Gcm_auth_bytes = unit

let (va_code_Gcm_make_length_quad :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_ZeroXmm Prims.int_zero;
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg Prims.int_zero)
        (Vale_X64_Machine_s.OReg (Prims.of_int (11)));
      Vale_X64_InsBasic.va_code_IMul64
        (Vale_X64_Machine_s.OReg Prims.int_zero)
        (Vale_X64_Machine_s.OConst (Prims.of_int (8)));
      Vale_X64_InsVector.va_code_Pinsrq Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero) Prims.int_one;
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg Prims.int_zero)
        (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
      Vale_X64_InsBasic.va_code_IMul64
        (Vale_X64_Machine_s.OReg Prims.int_zero)
        (Vale_X64_Machine_s.OConst (Prims.of_int (8)));
      Vale_X64_InsVector.va_code_Pinsrq Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero) Prims.int_zero]
let (va_codegen_success_Gcm_make_length_quad :
  unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_ZeroXmm Prims.int_zero)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_Mov64
            (Vale_X64_Machine_s.OReg Prims.int_zero)
            (Vale_X64_Machine_s.OReg (Prims.of_int (11))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_IMul64
               (Vale_X64_Machine_s.OReg Prims.int_zero)
               (Vale_X64_Machine_s.OConst (Prims.of_int (8))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Pinsrq Prims.int_zero
                  (Vale_X64_Machine_s.OReg Prims.int_zero) Prims.int_one)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Mov64
                     (Vale_X64_Machine_s.OReg Prims.int_zero)
                     (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsBasic.va_codegen_success_IMul64
                        (Vale_X64_Machine_s.OReg Prims.int_zero)
                        (Vale_X64_Machine_s.OConst (Prims.of_int (8))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Pinsrq
                           Prims.int_zero
                           (Vale_X64_Machine_s.OReg Prims.int_zero)
                           Prims.int_zero) (Vale_X64_Decls.va_ttrue ())))))))

type ('vaus0, 'vauk) va_wp_Gcm_make_length_quad = unit

let (va_code_Compute_pad_to_128_bits :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.IfElse
         ((Vale_X64_Decls.va_cmp_lt
             (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
             (Vale_X64_Machine_s.OConst (Prims.of_int (8)))),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_PinsrqImm Prims.int_zero
                 Prims.int_zero Prims.int_one
                 (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (10)));
              Vale_X64_InsBasic.va_code_Shl64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (3)));
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OConst Prims.int_one);
              Vale_X64_InsBasic.va_code_Shl64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OConst Prims.int_one);
              Vale_X64_InsVector.va_code_Pextrq
                (Vale_X64_Machine_s.OReg (Prims.of_int (2))) Prims.int_zero
                Prims.int_zero;
              Vale_X64_InsBasic.va_code_And64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)));
              Vale_X64_InsVector.va_code_Pinsrq Prims.int_zero
                (Vale_X64_Machine_s.OReg (Prims.of_int (2))) Prims.int_zero]),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsBasic.va_code_Mov64
                 (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)));
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (8)));
              Vale_X64_InsBasic.va_code_Shl64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (3)));
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OConst Prims.int_one);
              Vale_X64_InsBasic.va_code_Shl64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OConst Prims.int_one);
              Vale_X64_InsVector.va_code_Pextrq
                (Vale_X64_Machine_s.OReg (Prims.of_int (2))) Prims.int_zero
                Prims.int_one;
              Vale_X64_InsBasic.va_code_And64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)));
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsVector.va_code_Pinsrq Prims.int_zero
                (Vale_X64_Machine_s.OReg (Prims.of_int (2))) Prims.int_one]))]
let (va_codegen_success_Compute_pad_to_128_bits :
  unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_PinsrqImm Prims.int_zero
            Prims.int_zero Prims.int_one
            (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
               (Vale_X64_Machine_s.OReg (Prims.of_int (10))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsBasic.va_codegen_success_Shl64
                  (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                  (Vale_X64_Machine_s.OConst (Prims.of_int (3))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Mov64
                     (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                     (Vale_X64_Machine_s.OConst Prims.int_one))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsBasic.va_codegen_success_Shl64
                        (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                        (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_Sub64
                           (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                           (Vale_X64_Machine_s.OConst Prims.int_one))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Pextrq
                              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                              Prims.int_zero Prims.int_zero)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_And64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (11))))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Pinsrq
                                    Prims.int_zero
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (2))) Prims.int_zero)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (2)))
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (10))))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsBasic.va_codegen_success_Sub64
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (2)))
                                          (Vale_X64_Machine_s.OConst
                                             (Prims.of_int (8))))
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsBasic.va_codegen_success_Shl64
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (2)))
                                             (Vale_X64_Machine_s.OConst
                                                (Prims.of_int (3))))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                (Vale_X64_Machine_s.OReg
                                                   (Prims.of_int (11)))
                                                (Vale_X64_Machine_s.OConst
                                                   Prims.int_one))
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsBasic.va_codegen_success_Shl64
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (11)))
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (2))))
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                      (Vale_X64_Machine_s.OReg
                                                         (Prims.of_int (11)))
                                                      (Vale_X64_Machine_s.OConst
                                                         Prims.int_one))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_Pextrq
                                                         (Vale_X64_Machine_s.OReg
                                                            (Prims.of_int (2)))
                                                         Prims.int_zero
                                                         Prims.int_one)
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsBasic.va_codegen_success_And64
                                                            (Vale_X64_Machine_s.OReg
                                                               (Prims.of_int (2)))
                                                            (Vale_X64_Machine_s.OReg
                                                               (Prims.of_int (11))))
                                                         (Vale_X64_InsVector.va_codegen_success_Pinsrq
                                                            Prims.int_zero
                                                            (Vale_X64_Machine_s.OReg
                                                               (Prims.of_int (2)))
                                                            Prims.int_one))))))))))))))))))
      (Vale_X64_Decls.va_ttrue ())

type ('vaus0, 'vauk) va_wp_Compute_pad_to_128_bits = unit

let (va_code_Ghash_extra_bytes :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [va_code_Compute_pad_to_128_bits ();
      Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (9));
      Vale_AES_X64_AESopt2.va_code_Ghash_register ()]
let (va_codegen_success_Ghash_extra_bytes : unit -> Vale_X64_Decls.va_pbool)
  =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Compute_pad_to_128_bits ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
            (Prims.of_int (9)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_AES_X64_AESopt2.va_codegen_success_Ghash_register ())
            (Vale_X64_Decls.va_ttrue ())))

type ('hkeysub, 'totalubytes, 'olduhash, 'huLE, 'completeduquads, 'vaus0,
  'vauk) va_wp_Ghash_extra_bytes = unit

let (va_code_Gcm_extra_bytes :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Mov128 Prims.int_zero (Prims.of_int (11));
      Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (9));
      Vale_AES_X64_AES.va_code_AESEncryptBlock alg;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (5))
        (Prims.of_int (4)) (Vale_X64_Machine_s.OReg Prims.int_zero)
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor Prims.int_zero (Prims.of_int (4));
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (5))
        (Vale_X64_Machine_s.OReg Prims.int_zero) Prims.int_zero
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      va_code_Ghash_extra_bytes ()]
let (va_codegen_success_Gcm_extra_bytes :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Mov128 Prims.int_zero
         (Prims.of_int (11)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
            (Prims.of_int (9)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_AES_X64_AES.va_codegen_success_AESEncryptBlock alg)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                  (Prims.of_int (5)) (Prims.of_int (4))
                  (Vale_X64_Machine_s.OReg Prims.int_zero) Prims.int_zero
                  Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Pxor Prims.int_zero
                     (Prims.of_int (4)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                        (Prims.of_int (5))
                        (Vale_X64_Machine_s.OReg Prims.int_zero)
                        Prims.int_zero Prims.int_zero
                        Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (va_codegen_success_Ghash_extra_bytes ())
                        (Vale_X64_Decls.va_ttrue ())))))))

type ('alg, 'inoutub, 'key, 'roundukeys, 'keysub, 'hkeysub, 'totalubytes,
  'olduhash, 'completeduquads, 'huLE, 'vaus0, 'vauk) va_wp_Gcm_extra_bytes =
  unit

let (va_code_Gcm_blocks_auth :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsBasic.va_code_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
         (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
      Vale_X64_InsBasic.va_code_IMul64
        (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      Vale_X64_InsVector.va_code_InitPshufbMask (Prims.of_int (9))
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)));
      va_code_Gcm_auth_bytes ();
      Vale_X64_Machine_s.Block [];
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (15)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_gt
            (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
            (Vale_X64_Machine_s.OReg (Prims.of_int (2)))),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (7))
                Prims.int_zero (Vale_X64_Machine_s.OReg Prims.int_one)
                Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
             Vale_X64_InsBasic.va_code_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
             Vale_X64_InsBasic.va_code_And64
               (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
               (Vale_X64_Machine_s.OConst (Prims.of_int (15)));
             va_code_Ghash_extra_bytes ();
             Vale_X64_Machine_s.Block []]), (Vale_X64_Machine_s.Block []))]
let (va_codegen_success_Gcm_blocks_auth : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsBasic.va_codegen_success_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
         (Vale_X64_Machine_s.OReg (Prims.of_int (3))))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_IMul64
            (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
            (Vale_X64_Machine_s.OConst (Prims.of_int (16))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_InitPshufbMask
               (Prims.of_int (9))
               (Vale_X64_Machine_s.OReg (Prims.of_int (10))))
            (Vale_X64_Decls.va_pbool_and
               (va_codegen_success_Gcm_auth_bytes ())
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Mov64
                     (Vale_X64_Machine_s.OReg (Prims.of_int (15)))
                     (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                           (Prims.of_int (7)) Prims.int_zero
                           (Vale_X64_Machine_s.OReg Prims.int_one)
                           Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsBasic.va_codegen_success_Mov64
                              (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_And64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                                 (Vale_X64_Machine_s.OConst
                                    (Prims.of_int (15))))
                              (va_codegen_success_Ghash_extra_bytes ()))))
                     (Vale_X64_Decls.va_ttrue ()))))))

type ('authub, 'abytesub, 'hkeysub, 'huLE, 'vaus0,
  'vauk) va_wp_Gcm_blocks_auth = unit

let (va_code_Compute_iv :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.IfElse
         ((Vale_X64_Decls.va_cmp_eq
             (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
             (Vale_X64_Machine_s.OConst (Prims.of_int (12)))),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (7))
                 Prims.int_zero (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                 Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsVector.va_code_InitPshufbMask Prims.int_one
                (Vale_X64_Machine_s.OReg Prims.int_zero);
              Vale_X64_InsVector.va_code_Pshufb Prims.int_zero Prims.int_one;
              Vale_X64_InsVector.va_code_PinsrdImm Prims.int_zero
                Prims.int_one Prims.int_zero
                (Vale_X64_Machine_s.OReg Prims.int_zero);
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (7))
                (Vale_X64_Machine_s.OReg (Prims.of_int (2))) Prims.int_zero
                Prims.int_zero Vale_Arch_HeapTypes_s.Secret]),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsBasic.va_code_Mov64
                 (Vale_X64_Machine_s.OReg Prims.int_zero)
                 (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
              Vale_X64_InsBasic.va_code_Add64
                (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (32)));
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg Prims.int_one)
                (Vale_X64_Machine_s.OReg (Prims.of_int (8)));
              va_code_Gcm_blocks_auth ();
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OReg Prims.int_zero);
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
                (Vale_X64_Machine_s.OConst Prims.int_zero);
              Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
              va_code_Gcm_make_length_quad ();
              Vale_AES_X64_AESopt2.va_code_Ghash_register ();
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (7))
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Prims.of_int (8)) Prims.int_zero
                Vale_Arch_HeapTypes_s.Secret]))]
let (va_codegen_success_Compute_iv : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Load128_buffer
            (Prims.of_int (7)) Prims.int_zero
            (Vale_X64_Machine_s.OReg (Prims.of_int (8))) Prims.int_zero
            Vale_Arch_HeapTypes_s.Secret)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_InitPshufbMask
               Prims.int_one (Vale_X64_Machine_s.OReg Prims.int_zero))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
                  Prims.int_one)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                     Prims.int_zero Prims.int_one Prims.int_zero
                     (Vale_X64_Machine_s.OReg Prims.int_zero))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                        (Prims.of_int (7))
                        (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                        Prims.int_zero Prims.int_zero
                        Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_Mov64
                           (Vale_X64_Machine_s.OReg Prims.int_zero)
                           (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsBasic.va_codegen_success_Add64
                              (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                              (Vale_X64_Machine_s.OConst (Prims.of_int (32))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_Mov64
                                 (Vale_X64_Machine_s.OReg Prims.int_one)
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (8))))
                              (Vale_X64_Decls.va_pbool_and
                                 (va_codegen_success_Gcm_blocks_auth ())
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (2)))
                                       (Vale_X64_Machine_s.OReg
                                          Prims.int_zero))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsBasic.va_codegen_success_Mov64
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (11)))
                                          (Vale_X64_Machine_s.OConst
                                             Prims.int_zero))
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsBasic.va_codegen_success_Mov64
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (13)))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (4))))
                                          (Vale_X64_Decls.va_pbool_and
                                             (va_codegen_success_Gcm_make_length_quad
                                                ())
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_AES_X64_AESopt2.va_codegen_success_Ghash_register
                                                   ())
                                                (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                   (Prims.of_int (7))
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (2)))
                                                   (Prims.of_int (8))
                                                   Prims.int_zero
                                                   Vale_Arch_HeapTypes_s.Secret)))))))))))))))
      (Vale_X64_Decls.va_ttrue ())

type ('ivub, 'ivuextraub, 'iv, 'j0ub, 'hkeysub, 'vaus0,
  'vauk) va_wp_Compute_iv = unit

let (va_code_Gcm_blocks :
  Vale_AES_AES_common_s.algorithm ->
    Prims.int ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    fun offset ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsBasic.va_code_Mov64
           (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
           (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
        Vale_X64_InsBasic.va_code_AddLea64
          (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
          (Vale_X64_Machine_s.OConst (Prims.of_int (32)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg Prims.int_one)
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + Prims.int_zero);
        va_code_Gcm_blocks_auth ();
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (8)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (16)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (24)));
        Vale_X64_InsBasic.va_code_Mov64
          (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
        Vale_X64_InsVector.va_code_Mov128 Prims.int_zero (Prims.of_int (9));
        Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (2))
          Prims.int_one (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
          Prims.int_zero Vale_Arch_HeapTypes_s.Public;
        Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
          (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
          Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
        Vale_AES_X64_AESopt.va_code_Load_one_lsb (Prims.of_int (10));
        Vale_X64_InsVector.va_code_VPaddd Prims.int_one Prims.int_one
          (Prims.of_int (10));
        Vale_AES_X64_AESGCM.va_code_AES_GCM_encrypt_6mult alg;
        Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
          (Prims.of_int (11)) (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
          (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
        Vale_X64_InsBasic.va_code_Mov64
          (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg Prims.int_zero)
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (32)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (40)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (48)));
        Vale_X64_InsBasic.va_code_Mov64
          (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
        Vale_X64_InsVector.va_code_InitPshufbMask (Prims.of_int (9))
          (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
        Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (11))
          (Prims.of_int (9));
        va_code_Gcm_blocks128 alg;
        Vale_X64_InsStack.va_code_Stack_lemma ();
        Vale_X64_InsBasic.va_code_Add64
          (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
          (Vale_X64_Machine_s.OStack
             ((Vale_X64_Machine_s.MReg
                 ((Vale_X64_Machine_s.Reg
                     (Prims.int_zero, (Prims.of_int (7)))),
                   (offset + (Prims.of_int (24))))),
               Vale_Arch_HeapTypes_s.Public));
        Vale_X64_InsBasic.va_code_IMul64
          (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
          (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (offset + (Prims.of_int (64)));
        Vale_X64_Machine_s.IfElse
          ((Vale_X64_Decls.va_cmp_gt
              (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (14)))),
            (Vale_X64_Machine_s.Block
               [Vale_X64_InsStack.va_code_Load64_stack
                  (Vale_X64_Machine_s.OReg Prims.int_zero)
                  (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                  (offset + (Prims.of_int (56)));
               Vale_X64_InsBasic.va_code_Mov64
                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                 (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
               Vale_X64_InsBasic.va_code_And64
                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                 (Vale_X64_Machine_s.OConst (Prims.of_int (15)));
               va_code_Gcm_extra_bytes alg;
               Vale_X64_Machine_s.Block []]), (Vale_X64_Machine_s.Block []));
        Vale_X64_InsBasic.va_code_Mov64
          (Vale_X64_Machine_s.OReg (Prims.of_int (11)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
        va_code_Gcm_make_length_quad ();
        Vale_AES_X64_AESopt2.va_code_Ghash_register ();
        Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
          Prims.int_zero (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
          Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
        va_code_Gctr_register alg;
        Vale_X64_Machine_s.Block []]
let (va_codegen_success_Gcm_blocks :
  Vale_AES_AES_common_s.algorithm -> Prims.int -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    fun offset ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsBasic.va_codegen_success_Mov64
           (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
           (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
        (Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsBasic.va_codegen_success_AddLea64
              (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
              (Vale_X64_Machine_s.OConst (Prims.of_int (32))))
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsStack.va_codegen_success_Load64_stack
                 (Vale_X64_Machine_s.OReg Prims.int_one)
                 (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                 (offset + Prims.int_zero))
              (Vale_X64_Decls.va_pbool_and
                 (va_codegen_success_Gcm_blocks_auth ())
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsStack.va_codegen_success_Load64_stack
                       (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                       (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                       (offset + (Prims.of_int (8))))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsStack.va_codegen_success_Load64_stack
                          (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                          (offset + (Prims.of_int (16))))
                       (Vale_X64_Decls.va_pbool_and
                          (Vale_X64_InsStack.va_codegen_success_Load64_stack
                             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                             (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                             (offset + (Prims.of_int (24))))
                          (Vale_X64_Decls.va_pbool_and
                             (Vale_X64_InsBasic.va_codegen_success_Mov64
                                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                                (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
                             (Vale_X64_Decls.va_pbool_and
                                (Vale_X64_InsVector.va_codegen_success_Mov128
                                   Prims.int_zero (Prims.of_int (9)))
                                (Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                      (Prims.of_int (2)) Prims.int_one
                                      (Vale_X64_Machine_s.OReg
                                         (Prims.of_int (8))) Prims.int_zero
                                      Vale_Arch_HeapTypes_s.Public)
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                         (Prims.of_int (3))
                                         (Vale_X64_Machine_s.OReg
                                            (Prims.of_int (6))) Prims.int_one
                                         Prims.int_zero
                                         Vale_Arch_HeapTypes_s.Secret)
                                      (Vale_X64_Decls.va_pbool_and
                                         (Vale_AES_X64_AESopt.va_codegen_success_Load_one_lsb
                                            (Prims.of_int (10)))
                                         (Vale_X64_Decls.va_pbool_and
                                            (Vale_X64_InsVector.va_codegen_success_VPaddd
                                               Prims.int_one Prims.int_one
                                               (Prims.of_int (10)))
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_AES_X64_AESGCM.va_codegen_success_AES_GCM_encrypt_6mult
                                                  alg)
                                               (Vale_X64_Decls.va_pbool_and
                                                  (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                     (Prims.of_int (3))
                                                     (Prims.of_int (11))
                                                     (Vale_X64_Machine_s.OReg
                                                        (Prims.of_int (6)))
                                                     (Prims.of_int (32))
                                                     Vale_Arch_HeapTypes_s.Secret)
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                        (Vale_X64_Machine_s.OReg
                                                           (Prims.of_int (8)))
                                                        (Vale_X64_Machine_s.OReg
                                                           (Prims.of_int (2))))
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                           (Vale_X64_Machine_s.OReg
                                                              Prims.int_zero)
                                                           (Vale_X64_Machine_s.OReg
                                                              (Prims.of_int (7)))
                                                           (offset +
                                                              (Prims.of_int (32))))
                                                        (Vale_X64_Decls.va_pbool_and
                                                           (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                              (Vale_X64_Machine_s.OReg
                                                                 (Prims.of_int (5)))
                                                              (Vale_X64_Machine_s.OReg
                                                                 (Prims.of_int (7)))
                                                              (offset +
                                                                 (Prims.of_int (40))))
                                                           (Vale_X64_Decls.va_pbool_and
                                                              (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                 (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (3)))
                                                                 (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                 (offset +
                                                                    (Prims.of_int (48))))
                                                              (Vale_X64_Decls.va_pbool_and
                                                                 (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                                    (
                                                                    Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (14)))
                                                                    (
                                                                    Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (3))))
                                                                 (Vale_X64_Decls.va_pbool_and
                                                                    (
                                                                    Vale_X64_InsVector.va_codegen_success_InitPshufbMask
                                                                    (Prims.of_int (9))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (12))))
                                                                    (
                                                                    Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pshufb
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (9)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Gcm_blocks128
                                                                    alg)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_Stack_lemma
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Add64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (14)))
                                                                    (Vale_X64_Machine_s.OStack
                                                                    ((Vale_X64_Machine_s.MReg
                                                                    ((Vale_X64_Machine_s.Reg
                                                                    (Prims.int_zero,
                                                                    (Prims.of_int (7)))),
                                                                    (offset +
                                                                    (Prims.of_int (24))))),
                                                                    Vale_Arch_HeapTypes_s.Public)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_IMul64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (14)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (16))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (13)))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                    (offset +
                                                                    (Prims.of_int (64))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                    (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero)
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                    (offset +
                                                                    (Prims.of_int (56))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (13))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_And64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (15))))
                                                                    (va_codegen_success_Gcm_extra_bytes
                                                                    alg))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (11)))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (15))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Gcm_make_length_quad
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_AES_X64_AESopt2.va_codegen_success_Ghash_register
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    (Prims.of_int (3))
                                                                    Prims.int_zero
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    Prims.int_zero
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Gctr_register
                                                                    alg)
                                                                    (Vale_X64_Decls.va_ttrue
                                                                    ())))))))))))))))))))))))))))))))))

type ('alg, 'offset, 'authub, 'abytesub, 'in128x6ub, 'out128x6ub, 'in128ub,
  'out128ub, 'inoutub, 'ivub, 'scratchub, 'key, 'roundukeys, 'keysub,
  'hkeysub, 'vaus0, 'vauk) va_wp_Gcm_blocks = unit

let (va_code_Gcm_blocks_wrapped :
  Vale_AES_AES_common_s.algorithm ->
    Prims.int ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    fun offset ->
      Vale_X64_Machine_s.Block
        [va_code_Gcm_blocks alg offset; Vale_X64_Machine_s.Block []]
let (va_codegen_success_Gcm_blocks_wrapped :
  Vale_AES_AES_common_s.algorithm -> Prims.int -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    fun offset ->
      Vale_X64_Decls.va_pbool_and (va_codegen_success_Gcm_blocks alg offset)
        (Vale_X64_Decls.va_ttrue ())

type ('alg, 'offset, 'authub, 'abytesub, 'in128x6ub, 'out128x6ub, 'in128ub,
  'out128ub, 'inoutub, 'ivub, 'iv, 'scratchub, 'key, 'roundukeys, 'keysub,
  'hkeysub, 'vaus0, 'vauk) va_wp_Gcm_blocks_wrapped = unit

let (va_code_Save_registers :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsStack.va_code_Push_Secret
         (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (14)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (6)));
      Vale_X64_InsStack.va_code_Push_Secret
        (Vale_X64_Machine_s.OReg Prims.int_one);
      if win
      then
        Vale_X64_Machine_s.Block
          [Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (15))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (14))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (13))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (12))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (11))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (10))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (9))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (8))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (7))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PushXmm_Secret (Prims.of_int (6))
            (Vale_X64_Machine_s.OReg Prims.int_zero)]
      else Vale_X64_Machine_s.Block []]
let (va_codegen_success_Save_registers :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsStack.va_codegen_success_Push_Secret
         (Vale_X64_Machine_s.OReg (Prims.of_int (15))))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsStack.va_codegen_success_Push_Secret
            (Vale_X64_Machine_s.OReg (Prims.of_int (14))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsStack.va_codegen_success_Push_Secret
               (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsStack.va_codegen_success_Push_Secret
                  (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsStack.va_codegen_success_Push_Secret
                     (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsStack.va_codegen_success_Push_Secret
                        (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsStack.va_codegen_success_Push_Secret
                           (Vale_X64_Machine_s.OReg (Prims.of_int (6))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsStack.va_codegen_success_Push_Secret
                              (Vale_X64_Machine_s.OReg Prims.int_one))
                           (Vale_X64_Decls.va_pbool_and
                              (if win
                               then
                                 Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                      (Prims.of_int (15))
                                      (Vale_X64_Machine_s.OReg Prims.int_zero))
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                         (Prims.of_int (14))
                                         (Vale_X64_Machine_s.OReg
                                            Prims.int_zero))
                                      (Vale_X64_Decls.va_pbool_and
                                         (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                            (Prims.of_int (13))
                                            (Vale_X64_Machine_s.OReg
                                               Prims.int_zero))
                                         (Vale_X64_Decls.va_pbool_and
                                            (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                               (Prims.of_int (12))
                                               (Vale_X64_Machine_s.OReg
                                                  Prims.int_zero))
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                  (Prims.of_int (11))
                                                  (Vale_X64_Machine_s.OReg
                                                     Prims.int_zero))
                                               (Vale_X64_Decls.va_pbool_and
                                                  (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                     (Prims.of_int (10))
                                                     (Vale_X64_Machine_s.OReg
                                                        Prims.int_zero))
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                        (Prims.of_int (9))
                                                        (Vale_X64_Machine_s.OReg
                                                           Prims.int_zero))
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                           (Prims.of_int (8))
                                                           (Vale_X64_Machine_s.OReg
                                                              Prims.int_zero))
                                                        (Vale_X64_Decls.va_pbool_and
                                                           (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                              (Prims.of_int (7))
                                                              (Vale_X64_Machine_s.OReg
                                                                 Prims.int_zero))
                                                           (Vale_X64_Decls.va_pbool_and
                                                              (Vale_X64_InsStack.va_codegen_success_PushXmm_Secret
                                                                 (Prims.of_int (6))
                                                                 (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                              (Vale_X64_Decls.va_ttrue
                                                                 ()))))))))))
                               else Vale_X64_Decls.va_ttrue ())
                              (Vale_X64_Decls.va_ttrue ())))))))))

type ('win, 'vaus0, 'vauk) va_wp_Save_registers = unit

let (va_code_Restore_registers :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [if win
       then
         Vale_X64_Machine_s.Block
           [Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (6))
              (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (7))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (8))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (9))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (10))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (11))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (12))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (13))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (14))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PopXmm_Secret (Prims.of_int (15))
             (Vale_X64_Machine_s.OReg Prims.int_zero)]
       else Vale_X64_Machine_s.Block [];
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg Prims.int_one);
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (6)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (14)));
      Vale_X64_InsStack.va_code_Pop_Secret
        (Vale_X64_Machine_s.OReg (Prims.of_int (15)))]
let (va_codegen_success_Restore_registers :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (if win
       then
         Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
              (Prims.of_int (6)) (Vale_X64_Machine_s.OReg Prims.int_zero))
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                 (Prims.of_int (7)) (Vale_X64_Machine_s.OReg Prims.int_zero))
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                    (Prims.of_int (8))
                    (Vale_X64_Machine_s.OReg Prims.int_zero))
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                       (Prims.of_int (9))
                       (Vale_X64_Machine_s.OReg Prims.int_zero))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                          (Prims.of_int (10))
                          (Vale_X64_Machine_s.OReg Prims.int_zero))
                       (Vale_X64_Decls.va_pbool_and
                          (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                             (Prims.of_int (11))
                             (Vale_X64_Machine_s.OReg Prims.int_zero))
                          (Vale_X64_Decls.va_pbool_and
                             (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                (Prims.of_int (12))
                                (Vale_X64_Machine_s.OReg Prims.int_zero))
                             (Vale_X64_Decls.va_pbool_and
                                (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                   (Prims.of_int (13))
                                   (Vale_X64_Machine_s.OReg Prims.int_zero))
                                (Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                      (Prims.of_int (14))
                                      (Vale_X64_Machine_s.OReg Prims.int_zero))
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                         (Prims.of_int (15))
                                         (Vale_X64_Machine_s.OReg
                                            Prims.int_zero))
                                      (Vale_X64_Decls.va_ttrue ()))))))))))
       else Vale_X64_Decls.va_ttrue ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsStack.va_codegen_success_Pop_Secret
            (Vale_X64_Machine_s.OReg Prims.int_one))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsStack.va_codegen_success_Pop_Secret
               (Vale_X64_Machine_s.OReg (Prims.of_int (6))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                  (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                     (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                        (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                           (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                              (Vale_X64_Machine_s.OReg (Prims.of_int (14))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (15))))
                              (Vale_X64_Decls.va_ttrue ())))))))))

type ('win, 'oldursp, 'olduxmm6, 'olduxmm7, 'olduxmm8, 'olduxmm9, 'olduxmm10,
  'olduxmm11, 'olduxmm12, 'olduxmm13, 'olduxmm14, 'olduxmm15, 'vaus0,
  'vauk) va_wp_Restore_registers = unit

let (va_code_Gcm_blocks_stdcall :
  Prims.bool ->
    Vale_AES_AES_common_s.algorithm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    fun alg ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsMem.va_code_CreateHeaplets ();
        Vale_X64_Machine_s.Block [];
        va_code_Save_registers win;
        if win
        then
          Vale_X64_Machine_s.Block
            [Vale_X64_InsBasic.va_code_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
               (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (8)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (9)));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (264));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (272));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (352))]
        else
          Vale_X64_Machine_s.Block
            [Vale_X64_InsStack.va_code_Load64_stack
               (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
               (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
               (Prims.of_int (144))];
        va_code_Gcm_blocks_wrapped alg
          (Vale_X64_Decls.total_if win (Prims.of_int (280))
             (Prims.of_int (72)));
        Vale_X64_InsStack.va_code_Load64_stack
          (Vale_X64_Machine_s.OReg (Prims.of_int (15)))
          (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
          (Vale_X64_Decls.total_if win (Prims.of_int (360))
             (Prims.of_int (152)));
        Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (4))
          (Vale_X64_Machine_s.OReg (Prims.of_int (15))) (Prims.of_int (8))
          Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
        va_code_Restore_registers win;
        Vale_X64_InsMem.va_code_DestroyHeaplets ()]
let (va_codegen_success_Gcm_blocks_stdcall :
  Prims.bool -> Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun win ->
    fun alg ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsMem.va_codegen_success_CreateHeaplets ())
        (Vale_X64_Decls.va_pbool_and (va_codegen_success_Save_registers win)
           (Vale_X64_Decls.va_pbool_and
              (if win
               then
                 Vale_X64_Decls.va_pbool_and
                   (Vale_X64_InsBasic.va_codegen_success_Mov64
                      (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                      (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
                   (Vale_X64_Decls.va_pbool_and
                      (Vale_X64_InsBasic.va_codegen_success_Mov64
                         (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                         (Vale_X64_Machine_s.OReg (Prims.of_int (3))))
                      (Vale_X64_Decls.va_pbool_and
                         (Vale_X64_InsBasic.va_codegen_success_Mov64
                            (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                            (Vale_X64_Machine_s.OReg (Prims.of_int (8))))
                         (Vale_X64_Decls.va_pbool_and
                            (Vale_X64_InsBasic.va_codegen_success_Mov64
                               (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                               (Vale_X64_Machine_s.OReg (Prims.of_int (9))))
                            (Vale_X64_Decls.va_pbool_and
                               (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                  (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                                  (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                                  (Prims.of_int (264)))
                               (Vale_X64_Decls.va_pbool_and
                                  (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                     (Vale_X64_Machine_s.OReg
                                        (Prims.of_int (9)))
                                     (Vale_X64_Machine_s.OReg
                                        (Prims.of_int (7)))
                                     (Prims.of_int (272)))
                                  (Vale_X64_Decls.va_pbool_and
                                     (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                        (Vale_X64_Machine_s.OReg
                                           (Prims.of_int (6)))
                                        (Vale_X64_Machine_s.OReg
                                           (Prims.of_int (7)))
                                        (Prims.of_int (352)))
                                     (Vale_X64_Decls.va_ttrue ())))))))
               else
                 Vale_X64_Decls.va_pbool_and
                   (Vale_X64_InsStack.va_codegen_success_Load64_stack
                      (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                      (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                      (Prims.of_int (144))) (Vale_X64_Decls.va_ttrue ()))
              (Vale_X64_Decls.va_pbool_and
                 (va_codegen_success_Gcm_blocks_wrapped alg
                    (Vale_X64_Decls.total_if win (Prims.of_int (280))
                       (Prims.of_int (72))))
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsStack.va_codegen_success_Load64_stack
                       (Vale_X64_Machine_s.OReg (Prims.of_int (15)))
                       (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                       (Vale_X64_Decls.total_if win (Prims.of_int (360))
                          (Prims.of_int (152))))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                          (Prims.of_int (4))
                          (Vale_X64_Machine_s.OReg (Prims.of_int (15)))
                          (Prims.of_int (8)) Prims.int_zero
                          Vale_Arch_HeapTypes_s.Secret)
                       (Vale_X64_Decls.va_pbool_and
                          (va_codegen_success_Restore_registers win)
                          (Vale_X64_Decls.va_pbool_and
                             (Vale_X64_InsMem.va_codegen_success_DestroyHeaplets
                                ()) (Vale_X64_Decls.va_ttrue ()))))))))
type ('vaub0, 'vaus0, 'win, 'alg, 'authub, 'authubytes, 'authunum, 'keysub,
  'ivub, 'iv, 'hkeysub, 'abytesub, 'in128x6ub, 'out128x6ub, 'len128x6unum,
  'in128ub, 'out128ub, 'len128unum, 'inoutub, 'plainunum, 'scratchub, 
  'tagub, 'key) va_req_Gcm_blocks_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'alg, 'authub, 'authubytes, 'authunum, 'keysub,
  'ivub, 'iv, 'hkeysub, 'abytesub, 'in128x6ub, 'out128x6ub, 'len128x6unum,
  'in128ub, 'out128ub, 'len128unum, 'inoutub, 'plainunum, 'scratchub, 
  'tagub, 'key, 'vausM, 'vaufM) va_ens_Gcm_blocks_stdcall = unit

type ('win, 'alg, 'authub, 'authubytes, 'authunum, 'keysub, 'ivub, 'iv,
  'hkeysub, 'abytesub, 'in128x6ub, 'out128x6ub, 'len128x6unum, 'in128ub,
  'out128ub, 'len128unum, 'inoutub, 'plainunum, 'scratchub, 'tagub, 'key,
  'vaus0, 'vauk) va_wp_Gcm_blocks_stdcall = unit

let (va_code_Compute_iv_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsMem.va_code_CreateHeaplets ();
      if win
      then
        Vale_X64_Machine_s.Block
          [Vale_X64_Machine_s.IfElse
             ((Vale_X64_Decls.va_cmp_eq
                 (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                 (Vale_X64_Machine_s.OConst (Prims.of_int (12)))),
               (Vale_X64_Machine_s.Block
                  [Vale_X64_InsStack.va_code_Push_Secret
                     (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
                  Vale_X64_InsStack.va_code_Push_Secret
                    (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (8)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (9)));
                  Vale_X64_InsStack.va_code_Load64_stack
                    (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                    (Prims.of_int (56));
                  Vale_X64_InsStack.va_code_Load64_stack
                    (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                    (Prims.of_int (64));
                  va_code_Compute_iv ();
                  Vale_X64_InsStack.va_code_Pop_Secret
                    (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
                  Vale_X64_InsStack.va_code_Pop_Secret
                    (Vale_X64_Machine_s.OReg (Prims.of_int (5)))]),
               (Vale_X64_Machine_s.Block
                  [va_code_Save_registers win;
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (8)));
                  Vale_X64_InsBasic.va_code_Mov64
                    (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (9)));
                  Vale_X64_InsStack.va_code_Load64_stack
                    (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                    (Prims.of_int (264));
                  Vale_X64_InsStack.va_code_Load64_stack
                    (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                    (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
                    (Prims.of_int (272));
                  va_code_Compute_iv ();
                  va_code_Restore_registers win]))]
      else
        Vale_X64_Machine_s.Block
          [Vale_X64_Machine_s.IfElse
             ((Vale_X64_Decls.va_cmp_eq
                 (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                 (Vale_X64_Machine_s.OConst (Prims.of_int (12)))),
               (Vale_X64_Machine_s.Block [va_code_Compute_iv ()]),
               (Vale_X64_Machine_s.Block
                  [va_code_Save_registers win;
                  va_code_Compute_iv ();
                  va_code_Restore_registers win]))];
      Vale_X64_InsMem.va_code_DestroyHeaplets ()]
let (va_codegen_success_Compute_iv_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsMem.va_codegen_success_CreateHeaplets ())
      (Vale_X64_Decls.va_pbool_and
         (if win
          then
            Vale_X64_Decls.va_pbool_and
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsStack.va_codegen_success_Push_Secret
                    (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsStack.va_codegen_success_Push_Secret
                       (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsBasic.va_codegen_success_Mov64
                          (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                          (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
                       (Vale_X64_Decls.va_pbool_and
                          (Vale_X64_InsBasic.va_codegen_success_Mov64
                             (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                             (Vale_X64_Machine_s.OReg (Prims.of_int (3))))
                          (Vale_X64_Decls.va_pbool_and
                             (Vale_X64_InsBasic.va_codegen_success_Mov64
                                (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                                (Vale_X64_Machine_s.OReg (Prims.of_int (8))))
                             (Vale_X64_Decls.va_pbool_and
                                (Vale_X64_InsBasic.va_codegen_success_Mov64
                                   (Vale_X64_Machine_s.OReg
                                      (Prims.of_int (2)))
                                   (Vale_X64_Machine_s.OReg
                                      (Prims.of_int (9))))
                                (Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                      (Vale_X64_Machine_s.OReg
                                         (Prims.of_int (8)))
                                      (Vale_X64_Machine_s.OReg
                                         (Prims.of_int (7)))
                                      (Prims.of_int (56)))
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                         (Vale_X64_Machine_s.OReg
                                            (Prims.of_int (9)))
                                         (Vale_X64_Machine_s.OReg
                                            (Prims.of_int (7)))
                                         (Prims.of_int (64)))
                                      (Vale_X64_Decls.va_pbool_and
                                         (va_codegen_success_Compute_iv ())
                                         (Vale_X64_Decls.va_pbool_and
                                            (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                               (Vale_X64_Machine_s.OReg
                                                  (Prims.of_int (4))))
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                  (Vale_X64_Machine_s.OReg
                                                     (Prims.of_int (5))))
                                               (Vale_X64_Decls.va_pbool_and
                                                  (va_codegen_success_Save_registers
                                                     win)
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                        (Vale_X64_Machine_s.OReg
                                                           (Prims.of_int (5)))
                                                        (Vale_X64_Machine_s.OReg
                                                           (Prims.of_int (2))))
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                           (Vale_X64_Machine_s.OReg
                                                              (Prims.of_int (4)))
                                                           (Vale_X64_Machine_s.OReg
                                                              (Prims.of_int (3))))
                                                        (Vale_X64_Decls.va_pbool_and
                                                           (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                              (Vale_X64_Machine_s.OReg
                                                                 (Prims.of_int (3)))
                                                              (Vale_X64_Machine_s.OReg
                                                                 (Prims.of_int (8))))
                                                           (Vale_X64_Decls.va_pbool_and
                                                              (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                                 (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (2)))
                                                                 (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9))))
                                                              (Vale_X64_Decls.va_pbool_and
                                                                 (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                    (
                                                                    Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (8)))
                                                                    (
                                                                    Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                    (Prims.of_int (264)))
                                                                 (Vale_X64_Decls.va_pbool_and
                                                                    (
                                                                    Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                    (Prims.of_int (272)))
                                                                    (
                                                                    Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Compute_iv
                                                                    ())
                                                                    (va_codegen_success_Restore_registers
                                                                    win))))))))))))))))))))
              (Vale_X64_Decls.va_ttrue ())
          else
            Vale_X64_Decls.va_pbool_and
              (Vale_X64_Decls.va_pbool_and (va_codegen_success_Compute_iv ())
                 (Vale_X64_Decls.va_pbool_and
                    (va_codegen_success_Save_registers win)
                    (Vale_X64_Decls.va_pbool_and
                       (va_codegen_success_Compute_iv ())
                       (va_codegen_success_Restore_registers win))))
              (Vale_X64_Decls.va_ttrue ()))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsMem.va_codegen_success_DestroyHeaplets ())
            (Vale_X64_Decls.va_ttrue ())))
type ('vaub0, 'vaus0, 'win, 'iv, 'ivub, 'numubytes, 'len, 'j0ub, 'ivuextraub,
  'hkeysub) va_req_Compute_iv_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'iv, 'ivub, 'numubytes, 'len, 'j0ub, 'ivuextraub,
  'hkeysub, 'vausM, 'vaufM) va_ens_Compute_iv_stdcall = unit

type ('win, 'iv, 'ivub, 'numubytes, 'len, 'j0ub, 'ivuextraub, 'hkeysub,
  'vaus0, 'vauk) va_wp_Compute_iv_stdcall = unit
