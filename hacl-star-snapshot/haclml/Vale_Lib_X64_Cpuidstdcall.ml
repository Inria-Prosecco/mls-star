open Prims
let (va_code_Check_aesni_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_aesni_support ()]
let (va_codegen_success_Check_aesni_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_aesni_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_aesni_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_aesni_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_aesni_stdcall = unit

let (va_code_Check_sha_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_sha_support ()]
let (va_codegen_success_Check_sha_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_sha_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_sha_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_sha_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_sha_stdcall = unit

let (va_code_Check_adx_bmi2_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_adx_bmi2_support ()]
let (va_codegen_success_Check_adx_bmi2_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_adx_bmi2_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_adx_bmi2_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_adx_bmi2_stdcall =
  unit

type ('win, 'vaus0, 'vauk) va_wp_Check_adx_bmi2_stdcall = unit

let (va_code_Check_avx_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_avx_support ()]
let (va_codegen_success_Check_avx_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_avx_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_avx_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_avx_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_avx_stdcall = unit

let (va_code_Check_avx2_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_avx2_support ()]
let (va_codegen_success_Check_avx2_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_avx2_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_avx2_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_avx2_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_avx2_stdcall = unit

let (va_code_Check_movbe_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_movbe_support ()]
let (va_codegen_success_Check_movbe_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_movbe_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_movbe_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_movbe_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_movbe_stdcall = unit

let (va_code_Check_sse_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_sse_support ()]
let (va_codegen_success_Check_sse_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_sse_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_sse_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_sse_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_sse_stdcall = unit

let (va_code_Check_rdrand_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_rdrand_support ()]
let (va_codegen_success_Check_rdrand_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_rdrand_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_rdrand_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_rdrand_stdcall =
  unit

type ('win, 'vaus0, 'vauk) va_wp_Check_rdrand_stdcall = unit

let (va_code_Check_avx512_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_avx512_support ()]
let (va_codegen_success_Check_avx512_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_avx512_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_avx512_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_avx512_stdcall =
  unit

type ('win, 'vaus0, 'vauk) va_wp_Check_avx512_stdcall = unit

let (va_code_Check_osxsave_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_osxsave_support ()]
let (va_codegen_success_Check_osxsave_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_osxsave_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_osxsave_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_osxsave_stdcall =
  unit

type ('win, 'vaus0, 'vauk) va_wp_Check_osxsave_stdcall = unit

let (va_code_Check_avx_xcr0_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_avx_xcr0_support ()]
let (va_codegen_success_Check_avx_xcr0_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_avx_xcr0_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_avx_xcr0_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM, 'vaufM) va_ens_Check_avx_xcr0_stdcall =
  unit

type ('win, 'vaus0, 'vauk) va_wp_Check_avx_xcr0_stdcall = unit

let (va_code_Check_avx512_xcr0_stdcall :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_Lib_X64_Cpuid.va_code_Check_avx512_xcr0_support ()]
let (va_codegen_success_Check_avx512_xcr0_stdcall :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_Lib_X64_Cpuid.va_codegen_success_Check_avx512_xcr0_support ())
      (Vale_X64_Decls.va_ttrue ())
type ('vaub0, 'vaus0, 'win) va_req_Check_avx512_xcr0_stdcall = unit
type ('vaub0, 'vaus0, 'win, 'vausM,
  'vaufM) va_ens_Check_avx512_xcr0_stdcall = unit

type ('win, 'vaus0, 'vauk) va_wp_Check_avx512_xcr0_stdcall = unit
