open Prims
type rotc_t = FStar_UInt32.t
let (rotc_list : rotc_t Prims.list) =
  [Stdint.Uint32.one;
  (Stdint.Uint32.of_int (3));
  (Stdint.Uint32.of_int (6));
  (Stdint.Uint32.of_int (10));
  (Stdint.Uint32.of_int (15));
  (Stdint.Uint32.of_int (21));
  (Stdint.Uint32.of_int (28));
  (Stdint.Uint32.of_int (36));
  (Stdint.Uint32.of_int (45));
  (Stdint.Uint32.of_int (55));
  (Stdint.Uint32.of_int (2));
  (Stdint.Uint32.of_int (14));
  (Stdint.Uint32.of_int (27));
  (Stdint.Uint32.of_int (41));
  (Stdint.Uint32.of_int (56));
  (Stdint.Uint32.of_int (8));
  (Stdint.Uint32.of_int (25));
  (Stdint.Uint32.of_int (43));
  (Stdint.Uint32.of_int (62));
  (Stdint.Uint32.of_int (18));
  (Stdint.Uint32.of_int (39));
  (Stdint.Uint32.of_int (61));
  (Stdint.Uint32.of_int (20));
  (Stdint.Uint32.of_int (44))]
let (keccak_rotc : (rotc_t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list
    [Stdint.Uint32.one;
    (Stdint.Uint32.of_int (3));
    (Stdint.Uint32.of_int (6));
    (Stdint.Uint32.of_int (10));
    (Stdint.Uint32.of_int (15));
    (Stdint.Uint32.of_int (21));
    (Stdint.Uint32.of_int (28));
    (Stdint.Uint32.of_int (36));
    (Stdint.Uint32.of_int (45));
    (Stdint.Uint32.of_int (55));
    (Stdint.Uint32.of_int (2));
    (Stdint.Uint32.of_int (14));
    (Stdint.Uint32.of_int (27));
    (Stdint.Uint32.of_int (41));
    (Stdint.Uint32.of_int (56));
    (Stdint.Uint32.of_int (8));
    (Stdint.Uint32.of_int (25));
    (Stdint.Uint32.of_int (43));
    (Stdint.Uint32.of_int (62));
    (Stdint.Uint32.of_int (18));
    (Stdint.Uint32.of_int (39));
    (Stdint.Uint32.of_int (61));
    (Stdint.Uint32.of_int (20));
    (Stdint.Uint32.of_int (44))]
type piln_t = FStar_UInt32.t
let (piln_list : piln_t Prims.list) =
  [(Stdint.Uint32.of_int (10));
  (Stdint.Uint32.of_int (7));
  (Stdint.Uint32.of_int (11));
  (Stdint.Uint32.of_int (17));
  (Stdint.Uint32.of_int (18));
  (Stdint.Uint32.of_int (3));
  (Stdint.Uint32.of_int (5));
  (Stdint.Uint32.of_int (16));
  (Stdint.Uint32.of_int (8));
  (Stdint.Uint32.of_int (21));
  (Stdint.Uint32.of_int (24));
  (Stdint.Uint32.of_int (4));
  (Stdint.Uint32.of_int (15));
  (Stdint.Uint32.of_int (23));
  (Stdint.Uint32.of_int (19));
  (Stdint.Uint32.of_int (13));
  (Stdint.Uint32.of_int (12));
  (Stdint.Uint32.of_int (2));
  (Stdint.Uint32.of_int (20));
  (Stdint.Uint32.of_int (14));
  (Stdint.Uint32.of_int (22));
  (Stdint.Uint32.of_int (9));
  (Stdint.Uint32.of_int (6));
  Stdint.Uint32.one]
let (keccak_piln : (piln_t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list
    [(Stdint.Uint32.of_int (10));
    (Stdint.Uint32.of_int (7));
    (Stdint.Uint32.of_int (11));
    (Stdint.Uint32.of_int (17));
    (Stdint.Uint32.of_int (18));
    (Stdint.Uint32.of_int (3));
    (Stdint.Uint32.of_int (5));
    (Stdint.Uint32.of_int (16));
    (Stdint.Uint32.of_int (8));
    (Stdint.Uint32.of_int (21));
    (Stdint.Uint32.of_int (24));
    (Stdint.Uint32.of_int (4));
    (Stdint.Uint32.of_int (15));
    (Stdint.Uint32.of_int (23));
    (Stdint.Uint32.of_int (19));
    (Stdint.Uint32.of_int (13));
    (Stdint.Uint32.of_int (12));
    (Stdint.Uint32.of_int (2));
    (Stdint.Uint32.of_int (20));
    (Stdint.Uint32.of_int (14));
    (Stdint.Uint32.of_int (22));
    (Stdint.Uint32.of_int (9));
    (Stdint.Uint32.of_int (6));
    Stdint.Uint32.one]
let (rndc_list : FStar_UInt64.t Prims.list) =
  [Stdint.Uint64.one;
  (Stdint.Uint64.of_int (0x0000000000008082));
  (Stdint.Uint64.of_string "0x800000000000808a");
  (Stdint.Uint64.of_string "0x8000000080008000");
  (Stdint.Uint64.of_int (0x000000000000808b));
  (Stdint.Uint64.of_string "0x0000000080000001");
  (Stdint.Uint64.of_string "0x8000000080008081");
  (Stdint.Uint64.of_string "0x8000000000008009");
  (Stdint.Uint64.of_int (0x000000000000008a));
  (Stdint.Uint64.of_int (0x0000000000000088));
  (Stdint.Uint64.of_string "0x0000000080008009");
  (Stdint.Uint64.of_string "0x000000008000000a");
  (Stdint.Uint64.of_string "0x000000008000808b");
  (Stdint.Uint64.of_string "0x800000000000008b");
  (Stdint.Uint64.of_string "0x8000000000008089");
  (Stdint.Uint64.of_string "0x8000000000008003");
  (Stdint.Uint64.of_string "0x8000000000008002");
  (Stdint.Uint64.of_string "0x8000000000000080");
  (Stdint.Uint64.of_int (0x000000000000800a));
  (Stdint.Uint64.of_string "0x800000008000000a");
  (Stdint.Uint64.of_string "0x8000000080008081");
  (Stdint.Uint64.of_string "0x8000000000008080");
  (Stdint.Uint64.of_string "0x0000000080000001");
  (Stdint.Uint64.of_string "0x8000000080008008")]
let (keccak_rndc : (FStar_UInt64.t, unit) Lib_Sequence.lseq) =
  Lib_Sequence.of_list
    [Stdint.Uint64.one;
    (Stdint.Uint64.of_int (0x0000000000008082));
    (Stdint.Uint64.of_string "0x800000000000808a");
    (Stdint.Uint64.of_string "0x8000000080008000");
    (Stdint.Uint64.of_int (0x000000000000808b));
    (Stdint.Uint64.of_string "0x0000000080000001");
    (Stdint.Uint64.of_string "0x8000000080008081");
    (Stdint.Uint64.of_string "0x8000000000008009");
    (Stdint.Uint64.of_int (0x000000000000008a));
    (Stdint.Uint64.of_int (0x0000000000000088));
    (Stdint.Uint64.of_string "0x0000000080008009");
    (Stdint.Uint64.of_string "0x000000008000000a");
    (Stdint.Uint64.of_string "0x000000008000808b");
    (Stdint.Uint64.of_string "0x800000000000008b");
    (Stdint.Uint64.of_string "0x8000000000008089");
    (Stdint.Uint64.of_string "0x8000000000008003");
    (Stdint.Uint64.of_string "0x8000000000008002");
    (Stdint.Uint64.of_string "0x8000000000000080");
    (Stdint.Uint64.of_int (0x000000000000800a));
    (Stdint.Uint64.of_string "0x800000008000000a");
    (Stdint.Uint64.of_string "0x8000000080008081");
    (Stdint.Uint64.of_string "0x8000000000008080");
    (Stdint.Uint64.of_string "0x0000000080000001");
    (Stdint.Uint64.of_string "0x8000000080008008")]