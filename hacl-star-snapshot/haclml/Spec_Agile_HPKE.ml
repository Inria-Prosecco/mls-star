open Prims
let (is_valid_kem :
  (Spec_Agile_DH.algorithm * Spec_Hash_Definitions.hash_alg) -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | (Spec_Agile_DH.DH_Curve25519, Spec_Hash_Definitions.SHA2_256) -> true
    | (Spec_Agile_DH.DH_P256, Spec_Hash_Definitions.SHA2_256) -> true
    | (uu___1, uu___2) -> false
type aead =
  | Seal of Spec_Agile_AEAD.alg 
  | ExportOnly 
let (uu___is_Seal : aead -> Prims.bool) =
  fun projectee -> match projectee with | Seal alg -> true | uu___ -> false
let (__proj__Seal__item__alg : aead -> Spec_Agile_AEAD.alg) =
  fun projectee -> match projectee with | Seal alg -> alg
let (uu___is_ExportOnly : aead -> Prims.bool) =
  fun projectee -> match projectee with | ExportOnly -> true | uu___ -> false
let (is_valid_aead : aead -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Seal (Spec_Agile_AEAD.AES128_GCM) -> true
    | Seal (Spec_Agile_AEAD.AES256_GCM) -> true
    | Seal (Spec_Agile_AEAD.CHACHA20_POLY1305) -> true
    | ExportOnly -> true
    | uu___1 -> false
let (is_valid_hash : Spec_Hash_Definitions.hash_alg -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Spec_Hash_Definitions.SHA2_256 -> true
    | Spec_Hash_Definitions.SHA2_384 -> true
    | Spec_Hash_Definitions.SHA2_512 -> true
    | uu___1 -> false
type hash_algorithm = Spec_Hash_Definitions.algorithm
let (is_valid_ciphersuite :
  (Spec_Agile_DH.algorithm * hash_algorithm * aead *
    Spec_Hash_Definitions.algorithm) -> Prims.bool)
  =
  fun cs ->
    let uu___ = cs in
    match uu___ with
    | (kem_dh, kem_hash, aead1, hash) ->
        ((is_valid_kem (kem_dh, kem_hash)) && (is_valid_aead aead1)) &&
          (is_valid_hash hash)
type ciphersuite =
  (Spec_Agile_DH.algorithm * hash_algorithm * aead *
    Spec_Hash_Definitions.algorithm)
let (curve_of_cs : ciphersuite -> Spec_Agile_DH.algorithm) =
  fun cs ->
    let uu___ = cs in match uu___ with | (c, uu___1, uu___2, uu___3) -> c
let (kem_hash_of_cs : ciphersuite -> hash_algorithm) =
  fun cs ->
    let uu___ = cs in match uu___ with | (uu___1, h, uu___2, uu___3) -> h
let (aead_of_cs : ciphersuite -> aead) =
  fun cs ->
    let uu___ = cs in match uu___ with | (uu___1, uu___2, a, uu___3) -> a
let (hash_of_cs : ciphersuite -> hash_algorithm) =
  fun cs ->
    let uu___ = cs in match uu___ with | (uu___1, uu___2, uu___3, h) -> h
type mode =
  | Base 
  | PSK 
  | Auth 
  | AuthPSK 
let (uu___is_Base : mode -> Prims.bool) =
  fun projectee -> match projectee with | Base -> true | uu___ -> false
let (uu___is_PSK : mode -> Prims.bool) =
  fun projectee -> match projectee with | PSK -> true | uu___ -> false
let (uu___is_Auth : mode -> Prims.bool) =
  fun projectee -> match projectee with | Auth -> true | uu___ -> false
let (uu___is_AuthPSK : mode -> Prims.bool) =
  fun projectee -> match projectee with | AuthPSK -> true | uu___ -> false
let (size_label_version : Prims.nat) = (Prims.of_int (7))
let (label_version_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x48));
  FStar_UInt8.uint_to_t (Prims.of_int (0x50));
  FStar_UInt8.uint_to_t (Prims.of_int (0x4b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x45));
  FStar_UInt8.uint_to_t (Prims.of_int (0x2d));
  FStar_UInt8.uint_to_t (Prims.of_int (0x76));
  FStar_UInt8.uint_to_t (Prims.of_int (0x31))]
let (label_version : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_version_list
let (size_label_eae_prk : Prims.nat) = (Prims.of_int (7))
let (label_eae_prk_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x70));
  FStar_UInt8.uint_to_t (Prims.of_int (0x72));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6b))]
let (label_eae_prk : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_eae_prk_list
let (size_label_KEM : Prims.nat) = (Prims.of_int (3))
let (label_KEM_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x4b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x45));
  FStar_UInt8.uint_to_t (Prims.of_int (0x4d))]
let (label_KEM : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_KEM_list
let (size_label_HPKE : Prims.nat) = (Prims.of_int (4))
let (label_HPKE_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x48));
  FStar_UInt8.uint_to_t (Prims.of_int (0x50));
  FStar_UInt8.uint_to_t (Prims.of_int (0x4b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x45))]
let (label_HPKE : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_HPKE_list
let (size_label_shared_secret : Prims.nat) = (Prims.of_int (13))
let (label_shared_secret_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x68));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x72));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x64));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x63));
  FStar_UInt8.uint_to_t (Prims.of_int (0x72));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x74))]
let (label_shared_secret : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_shared_secret_list
let (size_label_psk_id_hash : Prims.nat) = (Prims.of_int (11))
let (label_psk_id_hash_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x70));
  FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x69));
  FStar_UInt8.uint_to_t (Prims.of_int (0x64));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x68));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x68))]
let (label_psk_id_hash : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_psk_id_hash_list
let (size_label_info_hash : Prims.nat) = (Prims.of_int (9))
let (label_info_hash_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x69));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6e));
  FStar_UInt8.uint_to_t (Prims.of_int (0x66));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x68));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x68))]
let (label_info_hash : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_info_hash_list
let (size_label_secret : Prims.nat) = (Prims.of_int (6))
let (label_secret_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x63));
  FStar_UInt8.uint_to_t (Prims.of_int (0x72));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x74))]
let (label_secret : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_secret_list
let (size_label_key : Prims.nat) = (Prims.of_int (3))
let (label_key_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x6b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x79))]
let (label_key : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_key_list
let (size_label_base_nonce : Prims.nat) = (Prims.of_int (10))
let (label_base_nonce_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x62));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6e));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6e));
  FStar_UInt8.uint_to_t (Prims.of_int (0x63));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65))]
let (label_base_nonce : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_base_nonce_list
let (size_label_exp : Prims.nat) = (Prims.of_int (3))
let (label_exp_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x78));
  FStar_UInt8.uint_to_t (Prims.of_int (0x70))]
let (label_exp : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_exp_list
let (size_label_sec : Prims.nat) = (Prims.of_int (3))
let (label_sec_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65));
  FStar_UInt8.uint_to_t (Prims.of_int (0x63))]
let (label_sec : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_sec_list
let (size_label_dkp_prk : Prims.nat) = (Prims.of_int (7))
let (label_dkp_prk_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x64));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6b));
  FStar_UInt8.uint_to_t (Prims.of_int (0x70));
  FStar_UInt8.uint_to_t (Prims.of_int (0x5f));
  FStar_UInt8.uint_to_t (Prims.of_int (0x70));
  FStar_UInt8.uint_to_t (Prims.of_int (0x72));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6b))]
let (label_dkp_prk : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_dkp_prk_list
let (size_label_candidate : Prims.nat) = (Prims.of_int (9))
let (label_candidate_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x63));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6e));
  FStar_UInt8.uint_to_t (Prims.of_int (0x64));
  FStar_UInt8.uint_to_t (Prims.of_int (0x69));
  FStar_UInt8.uint_to_t (Prims.of_int (0x64));
  FStar_UInt8.uint_to_t (Prims.of_int (0x61));
  FStar_UInt8.uint_to_t (Prims.of_int (0x74));
  FStar_UInt8.uint_to_t (Prims.of_int (0x65))]
let (label_candidate : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_candidate_list
let (size_label_sk : Prims.nat) = (Prims.of_int (2))
let (label_sk_list : FStar_UInt8.t Prims.list) =
  [FStar_UInt8.uint_to_t (Prims.of_int (0x73));
  FStar_UInt8.uint_to_t (Prims.of_int (0x6b))]
let (label_sk : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list label_sk_list
let (is_valid_not_export_only_ciphersuite : ciphersuite -> Prims.bool) =
  fun cs ->
    match aead_of_cs cs with | ExportOnly -> false | Seal uu___ -> true
type ciphersuite_not_export_only = ciphersuite
let (aead_alg_of : ciphersuite_not_export_only -> Spec_Agile_AEAD.alg) =
  fun cs -> match aead_of_cs cs with | Seal alg -> alg
let (size_aead_nonce : ciphersuite -> Prims.nat) =
  fun cs ->
    match aead_of_cs cs with
    | ExportOnly -> Prims.int_zero
    | Seal uu___ -> (Prims.of_int (12))
let (size_aead_key : ciphersuite -> Prims.nat) =
  fun cs ->
    match aead_of_cs cs with
    | ExportOnly -> Prims.int_zero
    | Seal uu___ -> Spec_Agile_AEAD.key_length (aead_alg_of cs)
let (size_aead_tag : ciphersuite -> Prims.nat) =
  fun cs ->
    match aead_of_cs cs with
    | ExportOnly -> Prims.int_zero
    | Seal uu___ -> Spec_Agile_AEAD.tag_length (aead_alg_of cs)
let (size_dh_key : ciphersuite -> Prims.nat) =
  fun cs ->
    match curve_of_cs cs with
    | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
    | Spec_Agile_DH.DH_P256 -> (Prims.of_int (32))
let (size_dh_public : ciphersuite -> Prims.nat) =
  fun cs ->
    match curve_of_cs cs with
    | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
    | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65))
let (size_kem_kdf : ciphersuite -> Prims.nat) =
  fun cs -> Spec_Hash_Definitions.size_hash (kem_hash_of_cs cs)
let (size_kem_key : ciphersuite -> Prims.nat) =
  fun cs -> Spec_Hash_Definitions.size_hash (kem_hash_of_cs cs)
let (size_kdf : ciphersuite -> Prims.nat) =
  fun cs -> Spec_Hash_Definitions.size_hash (hash_of_cs cs)
let (max_seq : ciphersuite -> Prims.nat) =
  fun cs ->
    match aead_of_cs cs with
    | ExportOnly -> Prims.int_zero
    | Seal uu___ ->
        (Prims.pow2
           ((Prims.of_int (8)) *
              (match aead_of_cs cs with
               | ExportOnly -> Prims.int_zero
               | Seal uu___1 -> (Prims.of_int (12)))))
          - Prims.int_one
let (size_suite_id_kem : Prims.nat) = (Prims.of_int (5))
let (size_suite_id_hpke : Prims.nat) = (Prims.of_int (10))
let (size_mode_identifier : Prims.nat) = Prims.int_one
let (size_ks_ctx : ciphersuite -> Prims.nat) =
  fun cs ->
    Prims.int_one +
      ((Prims.of_int (2)) * (Spec_Hash_Definitions.size_hash (hash_of_cs cs)))
let (labeled_extract_ikm_length_pred :
  hash_algorithm -> Prims.nat -> Prims.bool) =
  fun a ->
    fun ikm_length ->
      Spec_Agile_HKDF.extract_ikm_length_pred a
        ((Prims.of_int (7)) + ikm_length)



let (id_kem : ciphersuite -> (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun cs ->
    let uu___ = cs in
    match uu___ with
    | (kem_dh, kem_hash, uu___1, uu___2) ->
        (match (kem_dh, kem_hash) with
         | (Spec_Agile_DH.DH_P256, Spec_Hash_Definitions.SHA2_256) ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (16))))
         | (Spec_Agile_DH.DH_Curve25519, Spec_Hash_Definitions.SHA2_256) ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (32)))))
let (id_kdf : ciphersuite -> (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun cs ->
    let uu___ = cs in
    match uu___ with
    | (uu___1, uu___2, uu___3, h) ->
        (match h with
         | Spec_Hash_Definitions.SHA2_256 ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_one))
         | Spec_Hash_Definitions.SHA2_384 ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (2))))
         | Spec_Hash_Definitions.SHA2_512 ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (3)))))
let (id_aead : ciphersuite -> (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun cs ->
    let uu___ = cs in
    match uu___ with
    | (uu___1, uu___2, a, uu___3) ->
        (match a with
         | Seal (Spec_Agile_AEAD.AES128_GCM) ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_one))
         | Seal (Spec_Agile_AEAD.AES256_GCM) ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (2))))
         | Seal (Spec_Agile_AEAD.CHACHA20_POLY1305) ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t Prims.int_zero))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (3))))
         | ExportOnly ->
             Lib_Sequence.op_At_Bar Prims.int_one Prims.int_one
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (255))))
               (Lib_Sequence.create Prims.int_one
                  (FStar_UInt8.uint_to_t (Prims.of_int (255)))))
let (suite_id_kem : ciphersuite -> (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun cs -> FStar_Seq_Base.append label_KEM (id_kem cs)
let (suite_id_hpke : ciphersuite -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun cs ->
    FStar_Seq_Base.append label_HPKE
      (Lib_Sequence.op_At_Bar (Prims.of_int (2)) (Prims.of_int (4))
         (id_kem cs)
         (Lib_Sequence.op_At_Bar (Prims.of_int (2)) (Prims.of_int (2))
            (id_kdf cs) (id_aead cs)))
let (id_of_mode : mode -> (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun m ->
    match m with
    | Base ->
        Lib_Sequence.create Prims.int_one
          (FStar_UInt8.uint_to_t Prims.int_zero)
    | PSK ->
        Lib_Sequence.create Prims.int_one
          (FStar_UInt8.uint_to_t Prims.int_one)
    | Auth ->
        Lib_Sequence.create Prims.int_one
          (FStar_UInt8.uint_to_t (Prims.of_int (2)))
    | AuthPSK ->
        Lib_Sequence.create Prims.int_one
          (FStar_UInt8.uint_to_t (Prims.of_int (3)))
let (labeled_extract :
  hash_algorithm ->
    FStar_UInt8.t Lib_Sequence.seq ->
      FStar_UInt8.t Lib_Sequence.seq ->
        FStar_UInt8.t Lib_Sequence.seq ->
          FStar_UInt8.t Lib_Sequence.seq ->
            (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun suite_id ->
      fun salt ->
        fun label ->
          fun ikm ->
            let labeled_ikm1 = FStar_Seq_Base.append label_version suite_id in
            let labeled_ikm2 = FStar_Seq_Base.append labeled_ikm1 label in
            let labeled_ikm3 = FStar_Seq_Base.append labeled_ikm2 ikm in
            Spec_Agile_HKDF.extract a salt labeled_ikm3
let (labeled_expand_info_length_pred :
  hash_algorithm -> Prims.nat -> Prims.bool) =
  fun a ->
    fun info_length ->
      Spec_Agile_HKDF.expand_info_length_pred a
        ((Prims.of_int (9)) + info_length)
let (labeled_expand :
  hash_algorithm ->
    FStar_UInt8.t Lib_Sequence.seq ->
      FStar_UInt8.t Lib_Sequence.seq ->
        FStar_UInt8.t Lib_Sequence.seq ->
          FStar_UInt8.t Lib_Sequence.seq ->
            Prims.nat -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun a ->
    fun suite_id ->
      fun prk ->
        fun label ->
          fun info ->
            fun l ->
              let labeled_info1 =
                Obj.magic
                  (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
                     Lib_IntTypes.SEC (Prims.of_int (2)) l) in
              let labeled_info2 =
                FStar_Seq_Base.append labeled_info1 label_version in
              let labeled_info3 =
                FStar_Seq_Base.append labeled_info2 suite_id in
              let labeled_info4 = FStar_Seq_Base.append labeled_info3 label in
              let labeled_info5 = FStar_Seq_Base.append labeled_info4 info in
              Spec_Agile_HKDF.expand a prk labeled_info5 l


let (hash_max_input_length : hash_algorithm -> Prims.int) =
  fun a ->
    match a with
    | Spec_Hash_Definitions.MD5 -> (Prims.parse_int "2305843009213693951")
    | Spec_Hash_Definitions.SHA1 -> (Prims.parse_int "2305843009213693951")
    | Spec_Hash_Definitions.SHA2_224 ->
        (Prims.parse_int "2305843009213693951")
    | Spec_Hash_Definitions.SHA2_256 ->
        (Prims.parse_int "2305843009213693951")
    | Spec_Hash_Definitions.SHA2_384 ->
        (Prims.parse_int "42535295865117307932921825928971026431")
    | Spec_Hash_Definitions.SHA2_512 ->
        (Prims.parse_int "42535295865117307932921825928971026431")
let (labeled_extract_max_length_ikm :
  hash_algorithm -> Prims.nat -> Prims.nat -> Prims.int) =
  fun a ->
    fun size_suite_id ->
      fun size_local_label ->
        ((((hash_max_input_length a) - (Prims.of_int (7))) - size_suite_id) -
           size_local_label)
          - (Spec_Hash_Definitions.block_length a)
let (labeled_expand_max_length_info :
  hash_algorithm -> Prims.nat -> Prims.nat -> Prims.int) =
  fun a ->
    fun size_suite_id ->
      fun size_local_label ->
        (((((((hash_max_input_length a) -
                (Spec_Hash_Definitions.hash_length a))
               - (Prims.of_int (2)))
              - (Prims.of_int (7)))
             - size_suite_id)
            - size_local_label)
           - Prims.int_one)
          - (Spec_Hash_Definitions.block_length a)
let (max_length_psk : hash_algorithm -> Prims.int) =
  fun a ->
    labeled_extract_max_length_ikm a (Prims.of_int (10)) (Prims.of_int (6))
let (max_length_psk_id : hash_algorithm -> Prims.int) =
  fun a ->
    labeled_extract_max_length_ikm a (Prims.of_int (10)) (Prims.of_int (11))
let (max_length_info : hash_algorithm -> Prims.int) =
  fun a ->
    labeled_extract_max_length_ikm a (Prims.of_int (10)) (Prims.of_int (9))
let (max_length_exp_ctx : hash_algorithm -> Prims.int) =
  fun a ->
    labeled_expand_max_length_info a (Prims.of_int (10)) (Prims.of_int (3))
let (max_length_dkp_ikm : hash_algorithm -> Prims.int) =
  fun a ->
    labeled_extract_max_length_ikm a (Prims.of_int (5)) (Prims.of_int (7))
type 'cs key_dh_public_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs key_dh_secret_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs key_kem_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs key_aead_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs nonce_aead_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs seq_aead_s = Prims.nat
type 'cs exporter_secret_s = (FStar_UInt8.t, unit) Lib_Sequence.lseq
type 'cs psk_s = FStar_UInt8.t Lib_Sequence.seq
type 'cs psk_id_s = FStar_UInt8.t Lib_Sequence.seq
type 'cs info_s = FStar_UInt8.t Lib_Sequence.seq
type 'cs exp_ctx_s = FStar_UInt8.t Lib_Sequence.seq
type 'cs dkp_ikm_s = FStar_UInt8.t Lib_Sequence.seq
let (extract_and_expand_dh_pred : ciphersuite -> Prims.nat -> Prims.bool) =
  fun cs ->
    fun dh_length ->
      labeled_extract_ikm_length_pred (kem_hash_of_cs cs)
        ((Prims.of_int (12)) + dh_length)
let (extract_and_expand_ctx_pred : ciphersuite -> Prims.nat -> Prims.bool) =
  fun cs ->
    fun ctx_length ->
      labeled_expand_info_length_pred (kem_hash_of_cs cs)
        ((Prims.of_int (18)) + ctx_length)
let (extract_and_expand :
  ciphersuite ->
    FStar_UInt8.t Lib_Sequence.seq ->
      FStar_UInt8.t Lib_Sequence.seq -> unit key_kem_s)
  =
  fun cs ->
    fun dh ->
      fun kem_context ->
        let eae_prk =
          labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs)
            Lib_ByteSequence.lbytes_empty label_eae_prk dh in
        labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) eae_prk
          label_shared_secret kem_context
          (Spec_Hash_Definitions.size_hash (kem_hash_of_cs cs))
let (deserialize_public_key :
  ciphersuite -> unit key_dh_public_s -> unit Spec_Agile_DH.serialized_point)
  =
  fun cs ->
    fun pk ->
      match curve_of_cs cs with
      | Spec_Agile_DH.DH_Curve25519 -> pk
      | Spec_Agile_DH.DH_P256 ->
          Lib_Sequence.sub
            (match curve_of_cs cs with
             | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65))) pk Prims.int_one
            (Prims.of_int (64))
let (serialize_public_key :
  ciphersuite -> unit Spec_Agile_DH.serialized_point -> unit key_dh_public_s)
  =
  fun cs ->
    fun pk ->
      match curve_of_cs cs with
      | Spec_Agile_DH.DH_Curve25519 -> pk
      | Spec_Agile_DH.DH_P256 ->
          Lib_Sequence.op_At_Bar Prims.int_one
            (match curve_of_cs cs with
             | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (64)))
            (Lib_Sequence.create Prims.int_one
               (FStar_UInt8.uint_to_t (Prims.of_int (4)))) pk
let rec (dkp_nist_p :
  ciphersuite ->
    (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
      FStar_UInt8.t ->
        (unit key_dh_secret_s * unit key_dh_public_s)
          FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun dkp_prk ->
      fun counter ->
        let counterbyte =
          Obj.magic
            (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
               Lib_IntTypes.SEC Prims.int_one
               (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                  (Obj.magic counter))) in
        let bytes =
          labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) dkp_prk
            label_candidate counterbyte
            (match curve_of_cs cs with
             | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (32))) in
        let bytes1 =
          Lib_Sequence.map2
            (match curve_of_cs cs with
             | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (32)))
            (fun a -> fun b -> FStar_UInt8.logand a b) bytes
            (FStar_Seq_Base.create
               (match curve_of_cs cs with
                | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
                | Spec_Agile_DH.DH_P256 -> (Prims.of_int (32)))
               (FStar_UInt8.uint_to_t (Prims.of_int (255)))) in
        let sk =
          Lib_ByteSequence.nat_from_intseq_be_ Lib_IntTypes.U8
            Lib_IntTypes.SEC (Obj.magic bytes1) in
        if (sk = Prims.int_zero) || (sk >= Spec_P256.prime)
        then
          (if
             (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                (Obj.magic counter))
               = (Prims.of_int (255))
           then FStar_Pervasives_Native.None
           else
             dkp_nist_p cs dkp_prk
               (FStar_UInt8.add counter (FStar_UInt8.uint_to_t Prims.int_one)))
        else
          (match Spec_Agile_DH.secret_to_public (curve_of_cs cs) bytes1 with
           | FStar_Pervasives_Native.Some pk ->
               FStar_Pervasives_Native.Some
                 (bytes1, (serialize_public_key cs pk))
           | FStar_Pervasives_Native.None ->
               if
                 (Lib_IntTypes.v Lib_IntTypes.U8 Lib_IntTypes.SEC
                    (Obj.magic counter))
                   = (Prims.of_int (255))
               then FStar_Pervasives_Native.None
               else
                 dkp_nist_p cs dkp_prk
                   (FStar_UInt8.add counter
                      (FStar_UInt8.uint_to_t Prims.int_one)))
let (derive_key_pair :
  ciphersuite ->
    unit dkp_ikm_s ->
      (unit key_dh_secret_s * unit key_dh_public_s)
        FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun ikm ->
      match curve_of_cs cs with
      | Spec_Agile_DH.DH_Curve25519 ->
          let dkp_prk =
            labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs)
              Lib_ByteSequence.lbytes_empty label_dkp_prk ikm in
          let sk =
            labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) dkp_prk
              label_sk Lib_ByteSequence.lbytes_empty
              (match curve_of_cs cs with
               | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
               | Spec_Agile_DH.DH_P256 -> (Prims.of_int (32))) in
          (match Spec_Agile_DH.secret_to_public (curve_of_cs cs) sk with
           | FStar_Pervasives_Native.Some pk ->
               FStar_Pervasives_Native.Some
                 (sk, (serialize_public_key cs pk)))
      | Spec_Agile_DH.DH_P256 ->
          let dkp_prk =
            labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs)
              Lib_ByteSequence.lbytes_empty label_dkp_prk ikm in
          dkp_nist_p cs dkp_prk (FStar_UInt8.uint_to_t Prims.int_zero)
type 'cs encryption_context =
  (unit key_aead_s * unit nonce_aead_s * unit seq_aead_s * unit
    exporter_secret_s)
type 'cs exp_len = Prims.nat
let (prepare_dh :
  ciphersuite ->
    unit Spec_Agile_DH.serialized_point ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun cs ->
    fun dh ->
      match curve_of_cs cs with
      | Spec_Agile_DH.DH_Curve25519 -> serialize_public_key cs dh
      | Spec_Agile_DH.DH_P256 ->
          Lib_Sequence.sub
            (match curve_of_cs cs with
             | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (64))) dh
            Prims.int_zero (Prims.of_int (32))
let (encap :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        (unit key_kem_s * unit key_dh_public_s)
          FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        match Spec_Agile_DH.secret_to_public (curve_of_cs cs) skE with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some pkE ->
            let enc = serialize_public_key cs pkE in
            (match Spec_Agile_DH.dh (curve_of_cs cs) skE pkR with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some dh ->
                 let pkRm = serialize_public_key cs pkR in
                 let kem_context =
                   Lib_Sequence.concat
                     (match curve_of_cs cs with
                      | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
                      | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65)))
                     (match curve_of_cs cs with
                      | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
                      | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65))) enc
                     pkRm in
                 let dhm = prepare_dh cs dh in
                 let shared_secret = extract_and_expand cs dhm kem_context in
                 FStar_Pervasives_Native.Some (shared_secret, enc))
let (decap :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s -> unit key_kem_s FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        let pkE = deserialize_public_key cs enc in
        match Spec_Agile_DH.dh (curve_of_cs cs) skR pkE with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some dh ->
            (match Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some pkR ->
                 let pkRm = serialize_public_key cs pkR in
                 let kem_context =
                   Lib_Sequence.concat
                     (match curve_of_cs cs with
                      | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
                      | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65)))
                     (match curve_of_cs cs with
                      | Spec_Agile_DH.DH_Curve25519 -> (Prims.of_int (32))
                      | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65))) enc
                     pkRm in
                 let dhm = prepare_dh cs dh in
                 let shared_secret = extract_and_expand cs dhm kem_context in
                 FStar_Pervasives_Native.Some shared_secret)
let (auth_encap :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit key_dh_secret_s ->
          (unit key_kem_s * unit key_dh_public_s)
            FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun skS ->
          match Spec_Agile_DH.secret_to_public (curve_of_cs cs) skE with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some pkE ->
              (match Spec_Agile_DH.dh (curve_of_cs cs) skE pkR with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some es ->
                   (match Spec_Agile_DH.dh (curve_of_cs cs) skS pkR with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some ss ->
                        let esm = prepare_dh cs es in
                        let ssm = prepare_dh cs ss in
                        let dh =
                          Lib_Sequence.concat (Prims.of_int (32))
                            (Prims.of_int (32)) esm ssm in
                        let enc = serialize_public_key cs pkE in
                        (match Spec_Agile_DH.secret_to_public
                                 (curve_of_cs cs) skS
                         with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some pkS ->
                             let pkSm = serialize_public_key cs pkS in
                             let pkRm = serialize_public_key cs pkR in
                             let kem_context =
                               Lib_Sequence.concat
                                 (match curve_of_cs cs with
                                  | Spec_Agile_DH.DH_Curve25519 ->
                                      (Prims.of_int (32))
                                  | Spec_Agile_DH.DH_P256 ->
                                      (Prims.of_int (65)))
                                 ((match curve_of_cs cs with
                                   | Spec_Agile_DH.DH_Curve25519 ->
                                       (Prims.of_int (32))
                                   | Spec_Agile_DH.DH_P256 ->
                                       (Prims.of_int (65)))
                                    +
                                    (match curve_of_cs cs with
                                     | Spec_Agile_DH.DH_Curve25519 ->
                                         (Prims.of_int (32))
                                     | Spec_Agile_DH.DH_P256 ->
                                         (Prims.of_int (65)))) enc
                                 (Lib_Sequence.concat
                                    (match curve_of_cs cs with
                                     | Spec_Agile_DH.DH_Curve25519 ->
                                         (Prims.of_int (32))
                                     | Spec_Agile_DH.DH_P256 ->
                                         (Prims.of_int (65)))
                                    (match curve_of_cs cs with
                                     | Spec_Agile_DH.DH_Curve25519 ->
                                         (Prims.of_int (32))
                                     | Spec_Agile_DH.DH_P256 ->
                                         (Prims.of_int (65))) pkRm pkSm) in
                             let shared_secret =
                               extract_and_expand cs dh kem_context in
                             FStar_Pervasives_Native.Some
                               (shared_secret, enc))))
let (auth_decap :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit Spec_Agile_DH.serialized_point ->
          unit key_kem_s FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun pkS ->
          let pkE = deserialize_public_key cs enc in
          match Spec_Agile_DH.dh (curve_of_cs cs) skR pkE with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some es ->
              (match Spec_Agile_DH.dh (curve_of_cs cs) skR pkS with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ss ->
                   let esm = prepare_dh cs es in
                   let ssm = prepare_dh cs ss in
                   let dh =
                     Lib_Sequence.concat (Prims.of_int (32))
                       (Prims.of_int (32)) esm ssm in
                   (match Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some pkR ->
                        let pkRm = serialize_public_key cs pkR in
                        let pkSm = serialize_public_key cs pkS in
                        let kem_context =
                          Lib_Sequence.concat
                            (match curve_of_cs cs with
                             | Spec_Agile_DH.DH_Curve25519 ->
                                 (Prims.of_int (32))
                             | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65)))
                            ((match curve_of_cs cs with
                              | Spec_Agile_DH.DH_Curve25519 ->
                                  (Prims.of_int (32))
                              | Spec_Agile_DH.DH_P256 -> (Prims.of_int (65)))
                               +
                               (match curve_of_cs cs with
                                | Spec_Agile_DH.DH_Curve25519 ->
                                    (Prims.of_int (32))
                                | Spec_Agile_DH.DH_P256 ->
                                    (Prims.of_int (65)))) enc
                            (Lib_Sequence.concat
                               (match curve_of_cs cs with
                                | Spec_Agile_DH.DH_Curve25519 ->
                                    (Prims.of_int (32))
                                | Spec_Agile_DH.DH_P256 ->
                                    (Prims.of_int (65)))
                               (match curve_of_cs cs with
                                | Spec_Agile_DH.DH_Curve25519 ->
                                    (Prims.of_int (32))
                                | Spec_Agile_DH.DH_P256 ->
                                    (Prims.of_int (65))) pkRm pkSm) in
                        let shared_secret =
                          extract_and_expand cs dh kem_context in
                        FStar_Pervasives_Native.Some shared_secret))
let (default_psk : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_ByteSequence.lbytes_empty
let (default_psk_id : (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  Lib_ByteSequence.lbytes_empty
let (build_context :
  ciphersuite ->
    mode ->
      (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq ->
          (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun cs ->
    fun m ->
      fun psk_id_hash ->
        fun info_hash ->
          let context = id_of_mode m in
          let context1 = FStar_Seq_Base.append context psk_id_hash in
          let context2 = FStar_Seq_Base.append context1 info_hash in context2
let (lbytes_equal :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt8.t Lib_Sequence.seq ->
        (FStar_UInt8.t, unit) Lib_Sequence.lseq -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      fun b1 ->
        fun b2 ->
          if
            Prims.op_Negation
              ((FStar_Seq_Base.length b1) = (FStar_Seq_Base.length b2))
          then false
          else
            (let res =
               Obj.magic
                 (Lib_ByteSequence.seq_eq_mask Lib_IntTypes.U8 l2 l2
                    (Obj.magic b1) (Obj.magic b2) l2) in
             res = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
let (verify_psk_inputs :
  ciphersuite ->
    mode ->
      (unit psk_s * unit psk_id_s) FStar_Pervasives_Native.option ->
        Prims.bool)
  =
  fun cs ->
    fun m ->
      fun opsk ->
        match (m, opsk) with
        | (Base, FStar_Pervasives_Native.None) -> true
        | (PSK, FStar_Pervasives_Native.Some uu___) -> true
        | (Auth, FStar_Pervasives_Native.None) -> true
        | (AuthPSK, FStar_Pervasives_Native.Some uu___) -> true
        | (uu___, uu___1) -> false
let (key_schedule :
  ciphersuite ->
    mode ->
      unit key_kem_s ->
        unit info_s ->
          (unit psk_s * unit psk_id_s) FStar_Pervasives_Native.option ->
            unit encryption_context)
  =
  fun cs ->
    fun m ->
      fun shared_secret ->
        fun info ->
          fun opsk ->
            let uu___ =
              match opsk with
              | FStar_Pervasives_Native.None -> (default_psk, default_psk_id)
              | FStar_Pervasives_Native.Some (psk, psk_id) -> (psk, psk_id) in
            match uu___ with
            | (psk, psk_id) ->
                let psk_id_hash =
                  labeled_extract (hash_of_cs cs) (suite_id_hpke cs)
                    Lib_ByteSequence.lbytes_empty label_psk_id_hash psk_id in
                let info_hash =
                  labeled_extract (hash_of_cs cs) (suite_id_hpke cs)
                    Lib_ByteSequence.lbytes_empty label_info_hash info in
                let context = build_context cs m psk_id_hash info_hash in
                let secret =
                  labeled_extract (hash_of_cs cs) (suite_id_hpke cs)
                    shared_secret label_secret psk in
                let exporter_secret =
                  labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret
                    label_exp context
                    (Spec_Hash_Definitions.size_hash (hash_of_cs cs)) in
                if is_valid_not_export_only_ciphersuite cs
                then
                  let key =
                    labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret
                      label_key context
                      (match aead_of_cs cs with
                       | ExportOnly -> Prims.int_zero
                       | Seal uu___1 ->
                           Spec_Agile_AEAD.key_length (aead_alg_of cs)) in
                  let base_nonce =
                    labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret
                      label_base_nonce context
                      (match aead_of_cs cs with
                       | ExportOnly -> Prims.int_zero
                       | Seal uu___1 -> (Prims.of_int (12))) in
                  (key, base_nonce, Prims.int_zero, exporter_secret)
                else
                  (Lib_ByteSequence.lbytes_empty,
                    Lib_ByteSequence.lbytes_empty, Prims.int_zero,
                    exporter_secret)
let (key_of_ctx : ciphersuite -> unit encryption_context -> unit key_aead_s)
  =
  fun cs ->
    fun ctx ->
      let uu___ = ctx in
      match uu___ with | (key, uu___1, uu___2, uu___3) -> key
let (base_nonce_of_ctx :
  ciphersuite -> unit encryption_context -> unit nonce_aead_s) =
  fun cs ->
    fun ctx ->
      let uu___ = ctx in
      match uu___ with | (uu___1, base_nonce, uu___2, uu___3) -> base_nonce
let (seq_of_ctx : ciphersuite -> unit encryption_context -> unit seq_aead_s)
  =
  fun cs ->
    fun ctx ->
      let uu___ = ctx in
      match uu___ with | (uu___1, uu___2, seq, uu___3) -> seq
let (exp_sec_of_ctx :
  ciphersuite -> unit encryption_context -> unit exporter_secret_s) =
  fun cs ->
    fun ctx ->
      let uu___ = ctx in
      match uu___ with | (uu___1, uu___2, uu___3, exp_sec) -> exp_sec
let (set_seq :
  ciphersuite ->
    unit encryption_context ->
      unit seq_aead_s ->
        (unit key_aead_s * unit nonce_aead_s * unit seq_aead_s * unit
          exporter_secret_s))
  =
  fun cs ->
    fun ctx ->
      fun seq ->
        let uu___ = ctx in
        match uu___ with
        | (key, base_nonce, uu___1, exp_sec) ->
            (key, base_nonce, seq, exp_sec)
let (context_export :
  ciphersuite ->
    unit encryption_context ->
      unit exp_ctx_s ->
        unit exp_len -> (FStar_UInt8.t, unit) Lib_Sequence.lseq)
  =
  fun cs ->
    fun ctx ->
      fun exp_ctx ->
        fun l ->
          let exp_sec = exp_sec_of_ctx cs ctx in
          labeled_expand (hash_of_cs cs) (suite_id_hpke cs) exp_sec label_sec
            exp_ctx l
let (context_compute_nonce :
  ciphersuite_not_export_only ->
    unit encryption_context -> unit seq_aead_s -> unit nonce_aead_s)
  =
  fun cs ->
    fun ctx ->
      fun seq ->
        let base_nonce = base_nonce_of_ctx cs ctx in
        let enc_seq =
          Obj.magic
            (Lib_ByteSequence.nat_to_intseq_be_ Lib_IntTypes.U8
               Lib_IntTypes.SEC
               (match aead_of_cs cs with
                | ExportOnly -> Prims.int_zero
                | Seal uu___ -> (Prims.of_int (12))) seq) in
        Spec_Loops.seq_map2 (fun a -> fun b -> FStar_UInt8.logxor a b)
          enc_seq base_nonce
let (context_increment_seq :
  ciphersuite_not_export_only ->
    unit encryption_context ->
      unit encryption_context FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun ctx ->
      let seq = seq_of_ctx cs ctx in
      if seq = (max_seq cs)
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (set_seq cs ctx (seq + Prims.int_one))
let (context_seal :
  ciphersuite_not_export_only ->
    unit encryption_context ->
      unit Spec_Agile_AEAD.ad ->
        unit Spec_Agile_AEAD.plain ->
          (unit encryption_context * unit Spec_Agile_AEAD.cipher)
            FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun ctx ->
      fun aad ->
        fun pt ->
          let key = key_of_ctx cs ctx in
          let seq = seq_of_ctx cs ctx in
          let nonce = context_compute_nonce cs ctx seq in
          let ct = Spec_Agile_AEAD.encrypt (aead_alg_of cs) key nonce aad pt in
          match context_increment_seq cs ctx with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some new_ctx ->
              FStar_Pervasives_Native.Some (new_ctx, ct)
let (context_open :
  ciphersuite_not_export_only ->
    unit encryption_context ->
      unit Spec_Agile_AEAD.ad ->
        unit Spec_Agile_AEAD.cipher ->
          (unit encryption_context * unit Spec_Agile_AEAD.plain)
            FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun ctx ->
      fun aad ->
        fun ct ->
          let key = key_of_ctx cs ctx in
          let seq = seq_of_ctx cs ctx in
          let nonce = context_compute_nonce cs ctx seq in
          match Spec_Agile_AEAD.decrypt (aead_alg_of cs) key nonce aad ct
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some pt ->
              (match context_increment_seq cs ctx with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some new_ctx ->
                   FStar_Pervasives_Native.Some (new_ctx, pt))
let (setupBaseS :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          (unit key_dh_public_s * unit encryption_context)
            FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          match encap cs skE pkR with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (shared_secret, enc) ->
              let enc_ctx =
                key_schedule cs Base shared_secret info
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some (enc, enc_ctx)
let (setupBaseR :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s -> unit encryption_context FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          let pkR = Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR in
          let shared_secret = decap cs enc skR in
          match (pkR, shared_secret) with
          | (FStar_Pervasives_Native.Some pkR1, FStar_Pervasives_Native.Some
             shared_secret1) ->
              FStar_Pervasives_Native.Some
                (key_schedule cs Base shared_secret1 info
                   FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
let (sealBase :
  ciphersuite_not_export_only ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.plain ->
              (unit key_dh_public_s * (unit, unit) Spec_Agile_AEAD.encrypted)
                FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun aad ->
            fun pt ->
              match setupBaseS cs skE pkR info with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (enc, ctx) ->
                  (match context_seal cs ctx aad pt with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some (uu___, ct) ->
                       FStar_Pervasives_Native.Some (enc, ct))
let (openBase :
  ciphersuite_not_export_only ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.cipher ->
              (unit, unit) Spec_Agile_AEAD.decrypted
                FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun aad ->
            fun ct ->
              match setupBaseR cs enc skR info with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some ctx ->
                  (match context_open cs ctx aad ct with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some (uu___, pt) ->
                       FStar_Pervasives_Native.Some pt)
let (sendExportBase :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              (unit key_dh_public_s * (FStar_UInt8.t, unit)
                Lib_Sequence.lseq) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              match setupBaseS cs skE pkR info with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (enc, ctx) ->
                  FStar_Pervasives_Native.Some
                    (enc, (context_export cs ctx exp_ctx l))
let (receiveExportBase :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              (FStar_UInt8.t, unit) Lib_Sequence.lseq
                FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              match setupBaseR cs enc skR info with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some ctx ->
                  FStar_Pervasives_Native.Some
                    (context_export cs ctx exp_ctx l)
let (setupPSKS :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit psk_s ->
            unit psk_id_s ->
              (unit key_dh_public_s * unit encryption_context)
                FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun psk ->
            fun psk_id ->
              match encap cs skE pkR with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (shared_secret, enc) ->
                  let enc_ctx =
                    key_schedule cs PSK shared_secret info
                      (FStar_Pervasives_Native.Some (psk, psk_id)) in
                  FStar_Pervasives_Native.Some (enc, enc_ctx)
let (setupPSKR :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit psk_s ->
            unit psk_id_s ->
              unit encryption_context FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun psk ->
            fun psk_id ->
              let pkR = Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR in
              let shared_secret = decap cs enc skR in
              match (pkR, shared_secret) with
              | (FStar_Pervasives_Native.Some pkR1,
                 FStar_Pervasives_Native.Some shared_secret1) ->
                  FStar_Pervasives_Native.Some
                    (key_schedule cs PSK shared_secret1 info
                       (FStar_Pervasives_Native.Some (psk, psk_id)))
              | uu___ -> FStar_Pervasives_Native.None
let (sealPSK :
  ciphersuite_not_export_only ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.plain ->
              unit psk_s ->
                unit psk_id_s ->
                  (unit key_dh_public_s * (unit, unit)
                    Spec_Agile_AEAD.encrypted) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun aad ->
            fun pt ->
              fun psk ->
                fun psk_id ->
                  match setupPSKS cs skE pkR info psk psk_id with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (enc, ctx) ->
                      (match context_seal cs ctx aad pt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some (uu___, ct) ->
                           FStar_Pervasives_Native.Some (enc, ct))
let (openPSK :
  ciphersuite_not_export_only ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.cipher ->
              unit psk_s ->
                unit psk_id_s ->
                  (unit, unit) Spec_Agile_AEAD.decrypted
                    FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun aad ->
            fun ct ->
              fun psk ->
                fun psk_id ->
                  match setupPSKR cs enc skR info psk psk_id with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some ctx ->
                      (match context_open cs ctx aad ct with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some (uu___, pt) ->
                           FStar_Pervasives_Native.Some pt)
let (sendExportPSK :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit psk_s ->
                unit psk_id_s ->
                  (unit key_dh_public_s * (FStar_UInt8.t, unit)
                    Lib_Sequence.lseq) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun psk ->
                fun psk_id ->
                  match setupPSKS cs skE pkR info psk psk_id with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (enc, ctx) ->
                      FStar_Pervasives_Native.Some
                        (enc, (context_export cs ctx exp_ctx l))
let (receiveExportPSK :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit psk_s ->
                unit psk_id_s ->
                  (FStar_UInt8.t, unit) Lib_Sequence.lseq
                    FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun psk ->
                fun psk_id ->
                  match setupPSKR cs enc skR info psk psk_id with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some ctx ->
                      FStar_Pervasives_Native.Some
                        (context_export cs ctx exp_ctx l)
let (setupAuthS :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit key_dh_secret_s ->
            (unit key_dh_public_s * unit encryption_context)
              FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun skS ->
            match auth_encap cs skE pkR skS with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (shared_secret, enc) ->
                let enc_ctx =
                  key_schedule cs Auth shared_secret info
                    FStar_Pervasives_Native.None in
                FStar_Pervasives_Native.Some (enc, enc_ctx)
let (setupAuthR :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit Spec_Agile_DH.serialized_point ->
            unit encryption_context FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun pkS ->
            let pkR = Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR in
            let shared_secret = auth_decap cs enc skR pkS in
            match (pkR, shared_secret) with
            | (FStar_Pervasives_Native.Some pkR1,
               FStar_Pervasives_Native.Some shared_secret1) ->
                FStar_Pervasives_Native.Some
                  (key_schedule cs Auth shared_secret1 info
                     FStar_Pervasives_Native.None)
            | uu___ -> FStar_Pervasives_Native.None
let (sealAuth :
  ciphersuite_not_export_only ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.plain ->
              unit key_dh_secret_s ->
                (unit key_dh_public_s * (unit, unit)
                  Spec_Agile_AEAD.encrypted) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun aad ->
            fun pt ->
              fun skS ->
                match setupAuthS cs skE pkR info skS with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (enc, ctx) ->
                    (match context_seal cs ctx aad pt with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (uu___, ct) ->
                         FStar_Pervasives_Native.Some (enc, ct))
let (openAuth :
  ciphersuite_not_export_only ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.cipher ->
              unit Spec_Agile_DH.serialized_point ->
                (unit, unit) Spec_Agile_AEAD.decrypted
                  FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun aad ->
            fun ct ->
              fun pkS ->
                match setupAuthR cs enc skR info pkS with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some ctx ->
                    (match context_open cs ctx aad ct with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (uu___, pt) ->
                         FStar_Pervasives_Native.Some pt)
let (sendExportAuth :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit key_dh_secret_s ->
                (unit key_dh_public_s * (FStar_UInt8.t, unit)
                  Lib_Sequence.lseq) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun skS ->
                match setupAuthS cs skE pkR info skS with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (enc, ctx) ->
                    FStar_Pervasives_Native.Some
                      (enc, (context_export cs ctx exp_ctx l))
let (receiveExportAuth :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit Spec_Agile_DH.serialized_point ->
                (FStar_UInt8.t, unit) Lib_Sequence.lseq
                  FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun pkS ->
                match setupAuthR cs enc skR info pkS with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some ctx ->
                    FStar_Pervasives_Native.Some
                      (context_export cs ctx exp_ctx l)
let (setupAuthPSKS :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit psk_s ->
            unit psk_id_s ->
              unit key_dh_secret_s ->
                (unit key_dh_public_s * unit encryption_context)
                  FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun psk ->
            fun psk_id ->
              fun skS ->
                match auth_encap cs skE pkR skS with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (shared_secret, enc) ->
                    let enc_ctx =
                      key_schedule cs AuthPSK shared_secret info
                        (FStar_Pervasives_Native.Some (psk, psk_id)) in
                    FStar_Pervasives_Native.Some (enc, enc_ctx)
let (setupAuthPSKR :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit psk_s ->
            unit psk_id_s ->
              unit Spec_Agile_DH.serialized_point ->
                unit encryption_context FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun psk ->
            fun psk_id ->
              fun pkS ->
                let pkR = Spec_Agile_DH.secret_to_public (curve_of_cs cs) skR in
                let shared_secret = auth_decap cs enc skR pkS in
                match (pkR, shared_secret) with
                | (FStar_Pervasives_Native.Some pkR1,
                   FStar_Pervasives_Native.Some shared_secret1) ->
                    FStar_Pervasives_Native.Some
                      (key_schedule cs AuthPSK shared_secret1 info
                         (FStar_Pervasives_Native.Some (psk, psk_id)))
                | uu___ -> FStar_Pervasives_Native.None
let (sealAuthPSK :
  ciphersuite_not_export_only ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.plain ->
              unit psk_s ->
                unit psk_id_s ->
                  unit key_dh_secret_s ->
                    (unit key_dh_public_s * (unit, unit)
                      Spec_Agile_AEAD.encrypted)
                      FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun aad ->
            fun pt ->
              fun psk ->
                fun psk_id ->
                  fun skS ->
                    match setupAuthPSKS cs skE pkR info psk psk_id skS with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (enc, ctx) ->
                        (match context_seal cs ctx aad pt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (uu___, ct) ->
                             FStar_Pervasives_Native.Some (enc, ct))
let (openAuthPSK :
  ciphersuite_not_export_only ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit Spec_Agile_AEAD.ad ->
            unit Spec_Agile_AEAD.cipher ->
              unit psk_s ->
                unit psk_id_s ->
                  unit Spec_Agile_DH.serialized_point ->
                    (unit, unit) Spec_Agile_AEAD.decrypted
                      FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun aad ->
            fun ct ->
              fun psk ->
                fun psk_id ->
                  fun pkS ->
                    match setupAuthPSKR cs enc skR info psk psk_id pkS with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some ctx ->
                        (match context_open cs ctx aad ct with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (uu___, pt) ->
                             FStar_Pervasives_Native.Some pt)
let (sendExportAuthPSK :
  ciphersuite ->
    unit key_dh_secret_s ->
      unit Spec_Agile_DH.serialized_point ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit psk_s ->
                unit psk_id_s ->
                  unit key_dh_secret_s ->
                    (unit key_dh_public_s * (FStar_UInt8.t, unit)
                      Lib_Sequence.lseq) FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun skE ->
      fun pkR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun psk ->
                fun psk_id ->
                  fun skS ->
                    match setupAuthPSKS cs skE pkR info psk psk_id skS with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (enc, ctx) ->
                        FStar_Pervasives_Native.Some
                          (enc, (context_export cs ctx exp_ctx l))
let (receiveExportAuthPSK :
  ciphersuite ->
    unit key_dh_public_s ->
      unit key_dh_secret_s ->
        unit info_s ->
          unit exp_ctx_s ->
            unit exp_len ->
              unit psk_s ->
                unit psk_id_s ->
                  unit Spec_Agile_DH.serialized_point ->
                    (FStar_UInt8.t, unit) Lib_Sequence.lseq
                      FStar_Pervasives_Native.option)
  =
  fun cs ->
    fun enc ->
      fun skR ->
        fun info ->
          fun exp_ctx ->
            fun l ->
              fun psk ->
                fun psk_id ->
                  fun pkS ->
                    match setupAuthPSKR cs enc skR info psk psk_id pkS with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some ctx ->
                        FStar_Pervasives_Native.Some
                          (context_export cs ctx exp_ctx l)