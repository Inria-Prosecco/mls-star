open Prims
let (va_code_VPolyAdd :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      Vale_X64_Machine_s.operand128 ->
        (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src1 ->
      fun src2 ->
        Vale_X64_Machine_s.Block
          [Vale_X64_InsVector.va_code_VPxor dst src1 src2]
let (va_codegen_success_VPolyAdd :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      Vale_X64_Machine_s.operand128 -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src1 ->
      fun src2 ->
        Vale_X64_Decls.va_pbool_and
          (Vale_X64_InsVector.va_codegen_success_VPxor dst src1 src2)
          (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src1, 'src2, 'vaus0, 'vauk) va_wp_VPolyAdd = unit

let (va_code_PolyAnd :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsVector.va_code_Pand dst (Vale_X64_Machine_s.OReg src)]
let (va_codegen_success_PolyAnd :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Pand dst
           (Vale_X64_Machine_s.OReg src)) (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src, 'vaus0, 'vauk) va_wp_PolyAnd = unit

let (va_code_VHigh64ToLow :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src ->
      Vale_X64_Machine_s.Block [Vale_X64_InsVector.va_code_Vpsrldq8 dst src]
let (va_codegen_success_VHigh64ToLow :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Vpsrldq8 dst src)
        (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src, 'vaus0, 'vauk) va_wp_VHigh64ToLow = unit

let (va_code_VLow64ToHigh :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src ->
      Vale_X64_Machine_s.Block [Vale_X64_InsVector.va_code_Vpslldq8 dst src]
let (va_codegen_success_VLow64ToHigh :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Vpslldq8 dst src)
        (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src, 'vaus0, 'vauk) va_wp_VLow64ToHigh = unit

let (va_code_VSwap :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsVector.va_code_VPalignr8 dst src src]
let (va_codegen_success_VSwap :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_VPalignr8 dst src src)
        (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src, 'vaus0, 'vauk) va_wp_VSwap = unit

let (va_code_VPolyMul :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      Vale_X64_Machine_s.reg_xmm ->
        Prims.bool ->
          Prims.bool ->
            (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp)
              Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src1 ->
      fun src2 ->
        fun src1Hi ->
          fun src2Hi ->
            Vale_X64_Machine_s.Block
              [Vale_X64_InsAes.va_code_VPclmulqdq dst src1 src2 src1Hi src2Hi]
let (va_codegen_success_VPolyMul :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Machine_s.reg_xmm ->
      Vale_X64_Machine_s.reg_xmm ->
        Prims.bool -> Prims.bool -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun src1 ->
      fun src2 ->
        fun src1Hi ->
          fun src2Hi ->
            Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsAes.va_codegen_success_VPclmulqdq dst src1 src2
                 src1Hi src2Hi) (Vale_X64_Decls.va_ttrue ())
type ('dst, 'src1, 'src2, 'src1Hi, 'src2Hi, 'vaus0, 'vauk) va_wp_VPolyMul =
  unit
