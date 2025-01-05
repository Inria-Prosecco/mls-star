open Prims
let (aesni_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.aesni_enabled")
let (avx_cpuid_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx_cpuid_enabled")
let (pclmulqdq_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.pclmulqdq_enabled")
let (avx2_cpuid_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx2_cpuid_enabled")
let (bmi2_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.bmi2_enabled")
let (avx512f_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx512f_enabled")
let (avx512dq_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx512dq_enabled")
let (adx_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.adx_enabled")
let (sha_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.sha_enabled")
let (avx512bw_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx512bw_enabled")
let (avx512vl_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx512vl_enabled")
let (sse2_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.sse2_enabled")
let (ssse3_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.ssse3_enabled")
let (sse4_1_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.sse4_1_enabled")
let (movbe_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.movbe_enabled")
let (osxsave_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.osxsave_enabled")
let (rdrand_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith "Not yet implemented: Vale.X64.CPU_Features_s.rdrand_enabled")
let (sse_enabled : Prims.bool) =
  (sse2_enabled && ssse3_enabled) && sse4_1_enabled
let (avx512_cpuid_enabled : Prims.bool) =
  ((avx512f_enabled && avx512dq_enabled) && avx512bw_enabled) &&
    avx512vl_enabled
let (cpuid :
  Vale_X64_Machine_s.reg_64 ->
    Vale_Def_Words_s.nat64 ->
      Vale_Def_Words_s.nat64 -> Vale_Def_Words_s.nat64)
  =
  fun r ->
    fun rax ->
      fun rcx ->
        failwith "Not yet implemented: Vale.X64.CPU_Features_s.cpuid"
let (sse_xcr0_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.sse_xcr0_enabled")
let (avx_xcr0_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.avx_xcr0_enabled")
let (opmask_xcr0_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.opmask_xcr0_enabled")
let (zmm_hi256_xcr0_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.zmm_hi256_xcr0_enabled")
let (hi16_zmm_xcr0_enabled : Prims.bool) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: Vale.X64.CPU_Features_s.hi16_zmm_xcr0_enabled")
let (xgetbv :
  Vale_X64_Machine_s.reg_64 ->
    Vale_Def_Words_s.nat64 -> Vale_Def_Words_s.nat64)
  =
  fun r ->
    fun rcx -> failwith "Not yet implemented: Vale.X64.CPU_Features_s.xgetbv"
let (avx_xcr0 : Prims.bool) = sse_xcr0_enabled && avx_xcr0_enabled
let (avx512_xcr0 : Prims.bool) =
  ((avx_xcr0_enabled && opmask_xcr0_enabled) && zmm_hi256_xcr0_enabled) &&
    hi16_zmm_xcr0_enabled
let (avx_enabled : Prims.bool) = avx_cpuid_enabled && avx_xcr0
let (avx2_enabled : Prims.bool) = avx2_cpuid_enabled && avx_xcr0
let (avx512_enabled : Prims.bool) = avx512_cpuid_enabled && avx512_xcr0