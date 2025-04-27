MLS_HOME      ?= .
FSTAR_EXE     ?= fstar.exe
COMPARSE_HOME ?= $(MLS_HOME)/../comparse
DY_HOME       ?= $(MLS_HOME)/../dolev-yao-star

NO_DY ?=
USE_DY = $(if $(NO_DY),, 1)

INNER_SOURCE_DIRS = api bootstrap/code common/code common/proofs common/symbolic glue/code glue/proofs test treedem treekem/code treekem/proofs treemath treesync/code treesync/proofs $(if $(USE_DY), symbolic bootstrap/symbolic treesync/symbolic treekem/symbolic)

HACL_SNAPSHOT_DIR = $(MLS_HOME)/hacl-star-snapshot
SOURCE_DIRS = $(addprefix $(MLS_HOME)/fstar/, $(INNER_SOURCE_DIRS))

DY_INCLUDE_DIRS = core lib lib/communication lib/comparse lib/crypto lib/event lib/hpke lib/state lib/utils
INCLUDE_DIRS = $(SOURCE_DIRS) $(HACL_SNAPSHOT_DIR)/lib $(HACL_SNAPSHOT_DIR)/specs $(COMPARSE_HOME)/src $(if $(USE_DY), $(addprefix $(DY_HOME)/src/, $(DY_INCLUDE_DIRS)))
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +MLS +Comparse -Comparse.Tactic $(if $(USE_DY), +DY)'

# Allowed warnings:
# - (Warning 242) Definitions of inner let-rec ... and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types
# - (Warning 331) This name is being ignored
# - (Warning 335) Interface ... is admitted without an implementation 
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '@0..1000' --warn_error '+242+331-335' --cache_dir cache --odir obj --cmi $(OTHERFLAGS)

.PHONY: all clean

all: copy_lib

clean:
	rm -rf hints cache obj ml/lib/src ml/tests/src js/wasm js/js mls-*.tar.bz2
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

#
cache/MLS.%.checked: FSTAR_RULE_FLAGS = --ext context_pruning
# MLS.Test is the only file allowing "(Warning 272) Top-level let-bindings must be total; this term may have effects"
cache/MLS.Test.fst.checked: FSTAR_RULE_FLAGS = --warn_error '+272'
# Allow more warning in dependencies
cache/Lib.IntTypes.fst.checked: FSTAR_RULE_FLAGS = --warn_error '+288+349'

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

# Test vectors

ALL_TEST_VECTORS = tree-math crypto-basics secret-tree message-protection key-schedule psk_secret transcript-hashes welcome tree-operations tree-validation treekem messages
ALL_TEST_VECTORS_JSON = $(addprefix test_vectors/data/, $(addsuffix .json, $(ALL_TEST_VECTORS)))

test_vectors/data:
	mkdir -p test_vectors/data

.PRECIOUS: test_vectors/data/%.json
test_vectors/data/%.json: test_vectors/git_commit | test_vectors/data
	wget https://raw.githubusercontent.com/mlswg/mls-implementations/$(shell cat test_vectors/git_commit)/test-vectors/$*.json -O $@

# Final binary

.PHONY: build check release

check: copy_lib copy_tests $(ALL_TEST_VECTORS_JSON)
	OCAMLRUNPARAM=b $(FSTAR_EXE) --ocamlenv dune runtest --force --no-buffer --display=quiet --profile=release

js: copy_lib copy_tests
	$(FSTAR_EXE) --ocamlenv dune build --profile=release
	cd js && ./import.sh
	cd js && ./package.sh


# Interactive mode support

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include $(MLS_HOME)/cache

