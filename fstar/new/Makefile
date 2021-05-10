ifndef FSTAR_HOME
	FSTAR_HOME=$(dir $(shell which fstar.exe))/..
endif
ifndef Z3
	Z3=$(shell which z3)
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

HACL_SNAPSHOT_DIR=../hacl-star-snapshot

MLS_SPEC=Utils TreeMath_Internal TreeMath Lib_Result Parser Crypto_Builtins NetworkTypes Crypto_Derived Tree TreeDEM Lib_Array TreeSync TreeKEM TreeSyncTreeKEMBinder TreeSync_Hash
MLS_TEST=Test_Utils Test_TreeMath Test_KeySchedule Test_TreeKEM Test
MLS_SPEC_FILES=$(addprefix out/, $(addsuffix .ml, $(MLS_SPEC)))
MLS_TEST_FILES=out/Test_Types.ml Test_Reader.ml $(addprefix out/, $(addsuffix .ml, $(MLS_TEST)))

.PHONY: all clean

all: test

#TODO: make it nicer and put the right dependencies
test: out/Parser.ml out/Crypto_Builtins.ml out/Crypto_Derived.ml Test.fst | bin out test_vectors
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --admit_smt_queries true --odir out --codegen OCaml --extract '* -FStar -Spec' Test.fst
	$(OCAMLOPT) -I out -I $(HACL_SNAPSHOT_DIR)/ml $(HACL_SNAPSHOT_DIR)/ml/libhaclml.cmxa $(MLS_SPEC_FILES) $(MLS_TEST_FILES) -o bin/test.exe
	./bin/test.exe

out/Parser.ml: Parser.fsti Parser.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Parser' Parser.fst

out/Crypto_Builtins.ml: Crypto.Builtins.fsti Crypto.Builtins.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Crypto.Builtins' Crypto.Builtins.fst

out/Crypto_Derived.ml: Crypto.Derived.fsti Crypto.Derived.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include $(HACL_SNAPSHOT_DIR)/lib --include $(HACL_SNAPSHOT_DIR)/specs --lax --odir out --codegen OCaml --extract 'Crypto.Derived' Crypto.Derived.fst

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
