.PHONY: all test copy

all: copy
	$(MAKE) -C new extract
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune build --profile=release

test: copy
	dune runtest --profile=release

copy:
	cp new/MLS_Test_*.ml new/obj
