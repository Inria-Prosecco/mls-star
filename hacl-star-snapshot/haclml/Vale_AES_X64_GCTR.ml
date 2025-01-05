open Prims
let (va_code_Init_ctr :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Pxor (Prims.of_int (4)) (Prims.of_int (4));
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (4)) Prims.int_one
        Prims.int_zero (Vale_X64_Machine_s.OReg (Prims.of_int (12)))]
let (va_codegen_success_Init_ctr : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Pxor (Prims.of_int (4))
         (Prims.of_int (4)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_PinsrdImm (Prims.of_int (4))
            Prims.int_one Prims.int_zero
            (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
         (Vale_X64_Decls.va_ttrue ()))

type ('vaus0, 'vauk) va_wp_Init_ctr = unit

let (va_code_Inc32 :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun one ->
      Vale_X64_Machine_s.Block [Vale_X64_InsVector.va_code_Paddd dst one]
let (va_codegen_success_Inc32 :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun one ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Paddd dst one)
        (Vale_X64_Decls.va_ttrue ())
type ('dst, 'one, 'vaus0, 'vauk) va_wp_Inc32 = unit

let (va_code_Gctr_register :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Mov128 Prims.int_zero (Prims.of_int (7));
      Vale_X64_InsVector.va_code_InitPshufbMask (Prims.of_int (2))
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (2));
      Vale_AES_X64_AES.va_code_AESEncryptBlock alg;
      Vale_X64_InsVector.va_code_Pxor Prims.int_one Prims.int_zero]
let (va_codegen_success_Gctr_register :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Mov128 Prims.int_zero
         (Prims.of_int (7)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_InitPshufbMask
            (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
               (Prims.of_int (2)))
            (Vale_X64_Decls.va_pbool_and
               (Vale_AES_X64_AES.va_codegen_success_AESEncryptBlock alg)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Pxor Prims.int_one
                     Prims.int_zero) (Vale_X64_Decls.va_ttrue ())))))

type ('alg, 'key, 'roundukeys, 'keysub, 'vaus0, 'vauk) va_wp_Gctr_register =
  unit

let (va_code_Gctr_core_body0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Mov128 Prims.int_zero (Prims.of_int (7));
      Vale_X64_InsVector.va_code_Pshufb Prims.int_zero (Prims.of_int (8));
      Vale_AES_X64_AES.va_code_AESEncryptBlock alg;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (2)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (2))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
        (Vale_X64_Machine_s.OConst Prims.int_one);
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      va_code_Inc32 (Prims.of_int (7)) (Prims.of_int (4))]
let (va_codegen_success_Gctr_core_body0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Mov128 Prims.int_zero
         (Prims.of_int (7)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Pshufb Prims.int_zero
            (Prims.of_int (8)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_AES_X64_AES.va_codegen_success_AESEncryptBlock alg)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                  Prims.int_zero (Prims.of_int (2))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (9))) Prims.int_zero
                  Vale_Arch_HeapTypes_s.Secret)
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
                           (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                           (Vale_X64_Machine_s.OConst Prims.int_one))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsBasic.va_codegen_success_Add64
                              (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                              (Vale_X64_Machine_s.OConst (Prims.of_int (16))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_Add64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                                 (Vale_X64_Machine_s.OConst
                                    (Prims.of_int (16))))
                              (Vale_X64_Decls.va_pbool_and
                                 (va_codegen_success_Inc32 (Prims.of_int (7))
                                    (Prims.of_int (4)))
                                 (Vale_X64_Decls.va_ttrue ()))))))))))

type ('vauold, 'alg, 'vauinublockuoffset, 'vauinuinub, 'vauinukey,
  'vauinukeysub, 'vauinuolduiv, 'vauinuoutub, 'vauinuroundukeys, 'vaus0,
  'vauk) va_wp_Gctr_core_body0 = unit

let (va_code_Gctr_core_while0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.While
         ((Vale_X64_Decls.va_cmp_ne
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OReg (Prims.of_int (2)))),
           (Vale_X64_Machine_s.Block [va_code_Gctr_core_body0 alg]))]
let (va_codegen_success_Gctr_core_while0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Gctr_core_body0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinublockuoffset, 'vauinuinub, 'vauinukey,
  'vauinukeysub, 'vauinuolduiv, 'vauinuoutub, 'vauinuroundukeys, 'vaus0,
  'vauk) va_wp_Gctr_core_while0 = unit

let (va_code_Gctr_core :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsBasic.va_code_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
         (Vale_X64_Machine_s.OConst Prims.int_zero);
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
        (Vale_X64_Machine_s.OReg Prims.int_one);
      va_code_Init_ctr ();
      va_code_Gctr_core_while0 alg]
let (va_codegen_success_Gctr_core :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsBasic.va_codegen_success_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
         (Vale_X64_Machine_s.OConst Prims.int_zero))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_Mov64
            (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
            (Vale_X64_Machine_s.OReg Prims.int_zero))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
               (Vale_X64_Machine_s.OReg Prims.int_one))
            (Vale_X64_Decls.va_pbool_and (va_codegen_success_Init_ctr ())
               (Vale_X64_Decls.va_pbool_and
                  (va_codegen_success_Gctr_core_while0 alg)
                  (Vale_X64_Decls.va_ttrue ())))))

type ('alg, 'inub, 'outub, 'blockuoffset, 'olduiv, 'key, 'roundukeys,
  'keysub, 'vaus0, 'vauk) va_wp_Gctr_core = unit

let (va_code_Gctr_core_opt :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_InitPshufbMask (Prims.of_int (8))
         (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
      Vale_X64_InsBasic.va_code_Shr64
        (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (2)));
      Vale_X64_InsBasic.va_code_And64
        (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (3)));
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_gt
            (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
            (Vale_X64_Machine_s.OConst Prims.int_zero)),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsBasic.va_code_Mov64
                (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                (Vale_X64_Machine_s.OReg Prims.int_zero);
             Vale_X64_InsBasic.va_code_Mov64
               (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
               (Vale_X64_Machine_s.OReg Prims.int_one);
             Vale_AES_X64_AESCTRplain.va_code_Aes_counter_loop alg;
             Vale_X64_InsBasic.va_code_Mov64
               (Vale_X64_Machine_s.OReg Prims.int_zero)
               (Vale_X64_Machine_s.OReg (Prims.of_int (9)));
             Vale_X64_InsBasic.va_code_Mov64
               (Vale_X64_Machine_s.OReg Prims.int_one)
               (Vale_X64_Machine_s.OReg (Prims.of_int (10)))]),
          (Vale_X64_Machine_s.Block []));
      va_code_Gctr_core alg]
let (va_codegen_success_Gctr_core_opt :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_InitPshufbMask
         (Prims.of_int (8)) (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_Mov64
            (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
            (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_Shr64
               (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
               (Vale_X64_Machine_s.OConst (Prims.of_int (2))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsBasic.va_codegen_success_And64
                  (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                  (Vale_X64_Machine_s.OConst (Prims.of_int (3))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsBasic.va_codegen_success_Mov64
                        (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
                        (Vale_X64_Machine_s.OReg Prims.int_zero))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_Mov64
                           (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                           (Vale_X64_Machine_s.OReg Prims.int_one))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_AES_X64_AESCTRplain.va_codegen_success_Aes_counter_loop
                              alg)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_Mov64
                                 (Vale_X64_Machine_s.OReg Prims.int_zero)
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (9))))
                              (Vale_X64_InsBasic.va_codegen_success_Mov64
                                 (Vale_X64_Machine_s.OReg Prims.int_one)
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (10))))))))
                  (Vale_X64_Decls.va_pbool_and
                     (va_codegen_success_Gctr_core alg)
                     (Vale_X64_Decls.va_ttrue ()))))))

type ('alg, 'inub, 'outub, 'key, 'roundukeys, 'keysub, 'vaus0,
  'vauk) va_wp_Gctr_core_opt = unit

let (va_code_Gctr_bytes_extra_work :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
         (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
         Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Mov128 Prims.int_one (Prims.of_int (2));
      va_code_Gctr_register alg;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) Prims.int_one
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret]
let (va_codegen_success_Gctr_bytes_extra_work :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Load128_buffer Prims.int_zero
         (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
         Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Mov128 Prims.int_one
            (Prims.of_int (2)))
         (Vale_X64_Decls.va_pbool_and (va_codegen_success_Gctr_register alg)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                  Prims.int_one (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
                  Prims.int_one Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_ttrue ()))))

type ('alg, 'icbuBE, 'inub, 'outub, 'key, 'roundukeys, 'keysub, 'origuinuptr,
  'origuoutuptr, 'numubytes, 'vaus0, 'vauk) va_wp_Gctr_bytes_extra_work =
  unit

let (va_code_Gctr_bytes_no_extra :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun alg -> Vale_X64_Machine_s.Block []
let (va_codegen_success_Gctr_bytes_no_extra :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg -> Vale_X64_Decls.va_ttrue ()

type ('alg, 'icbuBE, 'inub, 'outub, 'key, 'roundukeys, 'keysub, 'origuinuptr,
  'origuoutuptr, 'numubytes, 'vaus0, 'vauk) va_wp_Gctr_bytes_no_extra = 
  unit

let (va_code_Gctr_bytes :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsBasic.va_code_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
         (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
      Vale_X64_InsBasic.va_code_IMul64
        (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (16)));
      va_code_Gctr_core_opt alg;
      va_code_Gctr_bytes_no_extra alg;
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_gt
            (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
            (Vale_X64_Machine_s.OReg (Prims.of_int (6)))),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (2))
                Prims.int_one (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
                Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
             va_code_Gctr_register alg;
             Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (2))
               (Vale_X64_Machine_s.OReg (Prims.of_int (13))) Prims.int_one
               Prims.int_zero Vale_Arch_HeapTypes_s.Secret]),
          (Vale_X64_Machine_s.Block []))]
let (va_codegen_success_Gctr_bytes :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsBasic.va_codegen_success_Mov64
         (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
         (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_IMul64
            (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
            (Vale_X64_Machine_s.OConst (Prims.of_int (16))))
         (Vale_X64_Decls.va_pbool_and (va_codegen_success_Gctr_core_opt alg)
            (Vale_X64_Decls.va_pbool_and
               (va_codegen_success_Gctr_bytes_no_extra alg)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                        (Prims.of_int (2)) Prims.int_one
                        (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
                        Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (va_codegen_success_Gctr_register alg)
                        (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                           (Prims.of_int (2))
                           (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
                           Prims.int_one Prims.int_zero
                           Vale_Arch_HeapTypes_s.Secret)))
                  (Vale_X64_Decls.va_ttrue ())))))

type ('alg, 'inub, 'outub, 'inoutub, 'key, 'roundukeys, 'keysub, 'vaus0,
  'vauk) va_wp_Gctr_bytes = unit

let (va_code_Gctr_bytes_stdcall :
  Prims.bool ->
    Vale_AES_AES_common_s.algorithm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    fun alg ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsMem.va_code_CreateHeaplets ();
        Vale_X64_InsStack.va_code_Push_Secret
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
        else Vale_X64_Machine_s.Block [];
        if win
        then
          Vale_X64_Machine_s.Block
            [Vale_X64_InsStack.va_code_Load64_stack
               (Vale_X64_Machine_s.OReg Prims.int_zero)
               (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
               (Prims.of_int (272));
            Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
              (Prims.of_int (7)) (Vale_X64_Machine_s.OReg Prims.int_zero)
              Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg Prims.int_zero)
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg Prims.int_one)
              (Vale_X64_Machine_s.OReg (Prims.of_int (8)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (9)));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (264));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (280))]
        else
          Vale_X64_Machine_s.Block
            [Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
               (Prims.of_int (7))
               (Vale_X64_Machine_s.OReg (Prims.of_int (9))) Prims.int_zero
               Vale_Arch_HeapTypes_s.Secret;
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg Prims.int_zero)
              (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg Prims.int_one)
              (Vale_X64_Machine_s.OReg (Prims.of_int (3)));
            Vale_X64_InsBasic.va_code_Mov64
              (Vale_X64_Machine_s.OReg (Prims.of_int (13)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
            Vale_X64_InsStack.va_code_Load64_stack
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Vale_X64_Machine_s.OReg (Prims.of_int (7)))
              (Prims.of_int (72))];
        va_code_Gctr_bytes alg;
        if win
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
          (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
        Vale_X64_InsMem.va_code_DestroyHeaplets ()]
let (va_codegen_success_Gctr_bytes_stdcall :
  Prims.bool -> Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun win ->
    fun alg ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsMem.va_codegen_success_CreateHeaplets ())
        (Vale_X64_Decls.va_pbool_and
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
                                           (Vale_X64_Machine_s.OReg
                                              Prims.int_zero))
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
                                   (Vale_X64_Decls.va_pbool_and
                                      (if win
                                       then
                                         Vale_X64_Decls.va_pbool_and
                                           (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                              (Vale_X64_Machine_s.OReg
                                                 Prims.int_zero)
                                              (Vale_X64_Machine_s.OReg
                                                 (Prims.of_int (7)))
                                              (Prims.of_int (272)))
                                           (Vale_X64_Decls.va_pbool_and
                                              (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                 Prims.int_zero
                                                 (Prims.of_int (7))
                                                 (Vale_X64_Machine_s.OReg
                                                    Prims.int_zero)
                                                 Prims.int_zero
                                                 Vale_Arch_HeapTypes_s.Secret)
                                              (Vale_X64_Decls.va_pbool_and
                                                 (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                    (Vale_X64_Machine_s.OReg
                                                       Prims.int_zero)
                                                    (Vale_X64_Machine_s.OReg
                                                       (Prims.of_int (2))))
                                                 (Vale_X64_Decls.va_pbool_and
                                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                       (Vale_X64_Machine_s.OReg
                                                          Prims.int_one)
                                                       (Vale_X64_Machine_s.OReg
                                                          (Prims.of_int (8))))
                                                    (Vale_X64_Decls.va_pbool_and
                                                       (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                          (Vale_X64_Machine_s.OReg
                                                             (Prims.of_int (4)))
                                                          (Vale_X64_Machine_s.OReg
                                                             (Prims.of_int (3))))
                                                       (Vale_X64_Decls.va_pbool_and
                                                          (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                             (Vale_X64_Machine_s.OReg
                                                                (Prims.of_int (13)))
                                                             (Vale_X64_Machine_s.OReg
                                                                (Prims.of_int (9))))
                                                          (Vale_X64_Decls.va_pbool_and
                                                             (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                (Vale_X64_Machine_s.OReg
                                                                   (Prims.of_int (8)))
                                                                (Vale_X64_Machine_s.OReg
                                                                   (Prims.of_int (7)))
                                                                (Prims.of_int (264)))
                                                             (Vale_X64_Decls.va_pbool_and
                                                                (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                                   (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (2)))
                                                                   (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (7)))
                                                                   (Prims.of_int (280)))
                                                                (Vale_X64_Decls.va_ttrue
                                                                   ()))))))))
                                       else
                                         Vale_X64_Decls.va_pbool_and
                                           (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                              Prims.int_zero
                                              (Prims.of_int (7))
                                              (Vale_X64_Machine_s.OReg
                                                 (Prims.of_int (9)))
                                              Prims.int_zero
                                              Vale_Arch_HeapTypes_s.Secret)
                                           (Vale_X64_Decls.va_pbool_and
                                              (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                 (Vale_X64_Machine_s.OReg
                                                    Prims.int_zero)
                                                 (Vale_X64_Machine_s.OReg
                                                    (Prims.of_int (5))))
                                              (Vale_X64_Decls.va_pbool_and
                                                 (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                    (Vale_X64_Machine_s.OReg
                                                       Prims.int_one)
                                                    (Vale_X64_Machine_s.OReg
                                                       (Prims.of_int (3))))
                                                 (Vale_X64_Decls.va_pbool_and
                                                    (Vale_X64_InsBasic.va_codegen_success_Mov64
                                                       (Vale_X64_Machine_s.OReg
                                                          (Prims.of_int (13)))
                                                       (Vale_X64_Machine_s.OReg
                                                          (Prims.of_int (2))))
                                                    (Vale_X64_Decls.va_pbool_and
                                                       (Vale_X64_InsStack.va_codegen_success_Load64_stack
                                                          (Vale_X64_Machine_s.OReg
                                                             (Prims.of_int (2)))
                                                          (Vale_X64_Machine_s.OReg
                                                             (Prims.of_int (7)))
                                                          (Prims.of_int (72)))
                                                       (Vale_X64_Decls.va_ttrue
                                                          ()))))))
                                      (Vale_X64_Decls.va_pbool_and
                                         (va_codegen_success_Gctr_bytes alg)
                                         (Vale_X64_Decls.va_pbool_and
                                            (if win
                                             then
                                               Vale_X64_Decls.va_pbool_and
                                                 (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                    (Prims.of_int (6))
                                                    (Vale_X64_Machine_s.OReg
                                                       Prims.int_zero))
                                                 (Vale_X64_Decls.va_pbool_and
                                                    (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                       (Prims.of_int (7))
                                                       (Vale_X64_Machine_s.OReg
                                                          Prims.int_zero))
                                                    (Vale_X64_Decls.va_pbool_and
                                                       (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                          (Prims.of_int (8))
                                                          (Vale_X64_Machine_s.OReg
                                                             Prims.int_zero))
                                                       (Vale_X64_Decls.va_pbool_and
                                                          (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                             (Prims.of_int (9))
                                                             (Vale_X64_Machine_s.OReg
                                                                Prims.int_zero))
                                                          (Vale_X64_Decls.va_pbool_and
                                                             (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                (Prims.of_int (10))
                                                                (Vale_X64_Machine_s.OReg
                                                                   Prims.int_zero))
                                                             (Vale_X64_Decls.va_pbool_and
                                                                (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                   (Prims.of_int (11))
                                                                   (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                                (Vale_X64_Decls.va_pbool_and
                                                                   (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                    (Prims.of_int (12))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                                   (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                    (Prims.of_int (13))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                    (Prims.of_int (14))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsStack.va_codegen_success_PopXmm_Secret
                                                                    (Prims.of_int (15))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                                    (Vale_X64_Decls.va_ttrue
                                                                    ()))))))))))
                                             else Vale_X64_Decls.va_ttrue ())
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                  (Vale_X64_Machine_s.OReg
                                                     Prims.int_one))
                                               (Vale_X64_Decls.va_pbool_and
                                                  (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                     (Vale_X64_Machine_s.OReg
                                                        (Prims.of_int (6))))
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                        (Vale_X64_Machine_s.OReg
                                                           (Prims.of_int (5))))
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                           (Vale_X64_Machine_s.OReg
                                                              (Prims.of_int (4))))
                                                        (Vale_X64_Decls.va_pbool_and
                                                           (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                              (Vale_X64_Machine_s.OReg
                                                                 (Prims.of_int (12))))
                                                           (Vale_X64_Decls.va_pbool_and
                                                              (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                                 (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (13))))
                                                              (Vale_X64_Decls.va_pbool_and
                                                                 (Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                                    (
                                                                    Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (14))))
                                                                 (Vale_X64_Decls.va_pbool_and
                                                                    (
                                                                    Vale_X64_InsStack.va_codegen_success_Pop_Secret
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (15))))
                                                                    (
                                                                    Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsMem.va_codegen_success_DestroyHeaplets
                                                                    ())
                                                                    (Vale_X64_Decls.va_ttrue
                                                                    ()))))))))))))))))))))))
type ('vaub0, 'vaus0, 'win, 'alg, 'inub, 'numubytes, 'outub, 'inoutub,
  'keysub, 'ctrub, 'numublocks, 'key) va_req_Gctr_bytes_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'alg, 'inub, 'numubytes, 'outub, 'inoutub,
  'keysub, 'ctrub, 'numublocks, 'key, 'vausM,
  'vaufM) va_ens_Gctr_bytes_stdcall = unit

type ('win, 'alg, 'inub, 'numubytes, 'outub, 'inoutub, 'keysub, 'ctrub,
  'numublocks, 'key, 'vaus0, 'vauk) va_wp_Gctr_bytes_stdcall = unit
