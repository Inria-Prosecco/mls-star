ifndef FSTAR_HOME
	FSTAR_HOME=$(dir $(shell which fstar.exe))/..
endif
ifndef Z3
	Z3=$(shell which z3)
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

HACL_SNAPSHOT_DIR=../hacl-star-snapshot

VALE=Math_Poly2_Defs Math_Poly2_Bits Math_Poly2 Lib_Seqs Def_Words_Seq Def_Words_Two Def_Words_Four Def_Opaque Def_Words Def_Types AES_AES AES_GCTR AES_GF128 AES_GHash AES_GCM
VALE_FILES=$(addprefix $(HACL_SNAPSHOT_DIR)/ml/Vale_, $(addsuffix _s.ml, $(VALE)))

HACL_LIB=IntTypes LoopCombinators Sequence ByteSequence UpdateMulti
HACL_LIB_FILES=$(addprefix $(HACL_SNAPSHOT_DIR)/ml/Lib_, $(addsuffix .ml, $(HACL_LIB)))

HACL_SPEC_MISC=Loops
HACL_SPEC_DH=DH P256_Definitions P256_Lemmas P256 Curve25519 Agile_DH
HACL_SPEC_SIGN=ECDSAP256_Definition ECDSA
HACL_SPEC_HASH=SHA1 MD5 Hash_PadFinish SHA2_Constants SHA2 Blake2 Hash_Definitions Agile_Hash Agile_HMAC Agile_HKDF
HACL_SPEC_AEAD=Chacha20 Poly1305 Chacha20Poly1305 GaloisField AES Agile_Cipher Agile_AEAD
HACL_SPEC=$(HACL_SPEC_MISC) $(HACL_SPEC_DH) $(HACL_SPEC_SIGN) $(HACL_SPEC_HASH) $(HACL_SPEC_AEAD)
HACL_SPEC_FILES=out/HPKE.ml $(addprefix $(HACL_SNAPSHOT_DIR)/ml/Spec_, $(addsuffix .ml, $(HACL_SPEC)))

MLS_SPEC=TreeMath_Internal Lib_Result Parser Crypto_Builtins NetworkTypes Crypto_Derived
MLS_TEST=Test_Utils Test_TreeMath Test_KeySchedule Test
MLS_SPEC_FILES=$(addprefix out/, $(addsuffix .ml, $(MLS_SPEC)))
MLS_TEST_FILES=out/Test_Types.ml Test_Reader.ml $(addprefix out/, $(addsuffix .ml, $(MLS_TEST)))

.PHONY: all clean

all: test

#TODO: make it nicer and put the right dependencies
test: out/Parser.ml out/Crypto_Builtins.ml out/Crypto_Derived.ml out/HPKE.ml Test.fst | bin out test_vectors
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract '* -FStar -Spec' Test.fst
	sed -i 's/Lib_ByteSequence.bytes_empty/(FStar_Seq_Base.empty ())/g' out/*
	$(OCAMLOPT) -I out -I $(HACL_SNAPSHOT_DIR)/ml $(VALE_FILES) $(HACL_LIB_FILES) $(HACL_SPEC_FILES) $(MLS_SPEC_FILES) $(MLS_TEST_FILES) -o bin/test.exe
	./bin/test.exe

out/Parser.ml: Parser.fsti Parser.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Parser' Parser.fst

out/Crypto_Builtins.ml: Crypto.Builtins.fsti Crypto.Builtins.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Crypto.Builtins' Crypto.Builtins.fst

out/Crypto_Derived.ml: Crypto.Derived.fsti Crypto.Derived.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Crypto.Derived' Crypto.Derived.fst

out/HPKE.ml: HPKE.fsti HPKE.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'HPKE' HPKE.fst

out:
	mkdir -p out
bin:
	mkdir -p bin

test_vectors:
	mkdir -p test_vectors
	wget https://raw.githubusercontent.com/openmls/openmls/main/test_vectors/kat_treemath_openmls.json -O test_vectors/treemath.json
	wget https://raw.githubusercontent.com/openmls/openmls/main/test_vectors/kat_key_schedule_openmls.json -O test_vectors/key_schedule.json

clean:
	rm -rf out bin test_vectors Test_Reader.o
