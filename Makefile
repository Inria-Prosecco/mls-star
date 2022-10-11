MLS_HOME 	?= .
FSTAR_HOME 	?= $(dir $(shell which fstar.exe))/..
Z3 		?= $(shell which z3)
COMPARSE_HOME 	?= $(MLS_HOME)/../comparse
DY_HOME 	?= $(MLS_HOME)/../dolev-yao-star

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

INNER_SOURCE_DIRS = api common/code common/proofs glue symbolic test treedem treekem treemath treesync/code treesync/proofs treesync/symbolic

HACL_SNAPSHOT_DIR = $(MLS_HOME)/hacl-star-snapshot
SOURCE_DIRS = $(addprefix $(MLS_HOME)/fstar/, $(INNER_SOURCE_DIRS))


INCLUDE_DIRS = $(SOURCE_DIRS) $(HACL_SNAPSHOT_DIR)/lib $(HACL_SNAPSHOT_DIR)/specs $(COMPARSE_HOME)/src $(DY_HOME) $(DY_HOME)/symbolic
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

DY_EXTRACT = +CryptoLib +SecrecyLabels +ComparseGlue +LabeledCryptoAPI +CryptoEffect +GlobalRuntimeLib +LabeledRuntimeAPI
FSTAR_EXTRACT = --extract '-* +MLS +Comparse $(DY_EXTRACT) -Comparse.Tactic'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '+241@247+285' --cache_dir cache --odir obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	rm -rf hints cache obj ml/lib/src ml/tests/src
	dune clean

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend
endif


# Verification

hints:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction

ALL_LIB_ML_FILES = $(filter-out obj/MLS_Test%.ml,$(ALL_ML_FILES))
ALL_TEST_ML_FILES = $(filter obj/MLS_Test%.ml,$(ALL_ML_FILES))

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib extract_tests copy_tests

extract_lib: $(ALL_LIB_ML_FILES)

copy_lib: extract_lib
	mkdir -p ml/lib/src
	cp $(ALL_LIB_ML_FILES) ml/lib/src

extract_tests: $(ALL_TEST_ML_FILES)

copy_tests: extract_tests
	mkdir -p ml/tests/src
	cp $(MLS_HOME)/fstar/test/MLS_Test_*.ml ml/tests/src
	cp $(ALL_TEST_ML_FILES) ml/tests/src

# Final binary

.PHONY: build check release

build: copy_lib
	$(MAKE) -C fstar extract
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune build --profile=release

check: copy_lib copy_tests
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune runtest --no-buffer --profile=release

release:
	tar cjvf mls-js-$(shell date +%Y%m%d%H%M%z).tar.bz2 js/index.html js/index.js _build/default/js/MLS_JS.bc.js

# Interactive mode support

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include $(MLS_HOME)/cache
