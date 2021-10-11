.PHONY: all test
all:
	$(MAKE) -C new extract
	cp new/MLS_Test_*.ml new/obj
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune build

test:
	dune runtest
