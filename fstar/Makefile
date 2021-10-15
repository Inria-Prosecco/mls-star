.PHONY: all test copy release

all: copy
	$(MAKE) -C new extract
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune build --profile=release

test: all
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune runtest --profile=release

copy:
	cp new/MLS_Test_*.ml new/obj

release:
	tar cjvf mls-js-$(shell date +%Y%m%d%H%M%z).tar.bz2 js/index.html js/index.js _build/default/js/MLS_JS.bc.js
