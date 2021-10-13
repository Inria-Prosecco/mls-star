.PHONY: all test copy

all: copy
	$(MAKE) -C new extract
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune build --profile=release

test: all
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune runtest --profile=release

copy:
	cp new/MLS_Test_*.ml new/obj
