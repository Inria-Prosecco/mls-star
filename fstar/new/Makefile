ifndef FSTAR_HOME
	FSTAR_HOME=$(dir $(shell which fstar.exe))/..
endif
ifndef Z3
	Z3=$(shell which z3)
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

.PHONY: all clean

all: test

#TODO: make it nicer and put the right dependencies
test: Test.fst bin out test_vectors
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml --extract '* -FStar' Test.fst
	$(OCAMLOPT) -I out out/Test_Types.ml Test_Reader.ml out/Test_Utils.ml out/TreeMath_Internal.ml out/Test_TreeMath.ml out/Test.ml -o bin/test.exe
	./bin/test.exe

out:
	mkdir -p out
bin:
	mkdir -p bin

test_vectors:
	mkdir -p test_vectors
	wget https://raw.githubusercontent.com/openmls/openmls/main/test_vectors/kat_treemath_openmls.json -O test_vectors/treemath.json

clean:
	rm -rf out bin test_vectors Test_Reader.o
