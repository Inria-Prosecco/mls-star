ifndef FSTAR_HOME
	FSTAR_HOME = $(dir $(shell which fstar.exe))/..
endif
ifndef Z3
	Z3 = $(shell which z3)
endif
ifndef COMPARSE_HOME
	COMPARSE_HOME = ../../comparse
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

HACL_SNAPSHOT_DIR = ../hacl-star-snapshot
SOURCE_DIR = .

INCLUDE_DIRS = $(HACL_SNAPSHOT_DIR)/lib $(HACL_SNAPSHOT_DIR)/specs $(COMPARSE_HOME)/src
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

FSTAR_EXTRACT = --extract '-* +MLS +Comparse -Comparse.Tactic'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '+241@247+285' --cache_dir obj --odir obj --cmi

.PHONY: all clean

all: extract

clean:
	rm -rf hints bin obj/*.ml obj/*.checked
	dune clean

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIR))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIR)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

# Verification

hints:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(ALL_ML_FILES)

# Final binary

bin:
	mkdir $@

.PHONY: test
bin/test.exe: test
test: test_vectors
	$(MAKE) -C .. test

# Test vectors

# test_vectors:
# 	wget https://tmp.twal.org/test_vectors.zip
# 	unzip test_vectors.zip

# Interactive mode support...

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include obj
