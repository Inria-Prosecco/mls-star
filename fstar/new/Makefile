ifndef FSTAR_HOME
	FSTAR_HOME = $(dir $(shell which fstar.exe))/..
endif
ifndef Z3
	Z3 = $(shell which z3)
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

HACL_SNAPSHOT_DIR = ../hacl-star-snapshot
SOURCE_DIR = .

INCLUDE_DIRS = $(HACL_SNAPSHOT_DIR)/lib $(HACL_SNAPSHOT_DIR)/specs
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

FSTAR_EXTRACT = --extract '-* +MLS'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --admit_smt_queries true --warn_error '+241@247+285' --odir out --cmi

.PHONY: all clean

all: bin/test.exe

clean:
	rm -rf hints out bin obj *.checked

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIR))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIR)))

ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
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

.PRECIOUS: out/%.ml
out/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))
out/MLS_Test_Reader.ml: MLS_Test_Reader.ml
	cp $< $@
out/MLS_Test_Equality.ml: MLS_Test_Equality.ml
	cp $< $@

# OCaml compilation

.PRECIOUS: out/%.cmx
out/%.cmx: out/%.ml
	$(OCAMLOPT) -I out -I $(HACL_SNAPSHOT_DIR)/ml $(HACL_SNAPSHOT_DIR)/ml/libhaclml.cmxa -c $< -o $@

out/MLS_Test_Reader.cmx: out/MLS_Test_Reader.ml out/MLS_Test_Types.cmx
out/MLS_Test_Equality.cmx: out/MLS_Test_Equality.ml

# Final binary

ALL_CMX_FILES=out/MLS_Test_Reader.cmx out/MLS_Test_Equality.cmx $(subst .ml,.cmx,$(ALL_ML_FILES))

bin/test.exe: out/MLS_Test.cmx | bin
	$(OCAMLOPT) -I out $(HACL_SNAPSHOT_DIR)/ml/libhaclml.cmxa $(ALL_CMX_FILES) -o bin/test.exe

bin:
	mkdir $@
