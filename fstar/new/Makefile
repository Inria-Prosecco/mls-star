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
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --admit_smt_queries true --warn_error '+241@247+285' --cache_dir obj --odir obj --cmi

.PHONY: all clean

all: bin/test.exe

clean:
	rm -rf hints bin obj

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

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))
obj/MLS_Test_Reader.ml: MLS_Test_Reader.ml
	cp $< $@
obj/MLS_Test_Equality.ml: MLS_Test_Equality.ml
	cp $< $@

extract: $(ALL_ML_FILES)

# OCaml compilation

.PRECIOUS: obj/%.cmx
obj/%.cmx: obj/%.ml
	$(OCAMLOPT) -I obj -I $(HACL_SNAPSHOT_DIR)/haclml $(HACL_SNAPSHOT_DIR)/haclml/libhaclml.cmxa -c $< -o $@

obj/MLS_Test_Reader.cmx: obj/MLS_Test_Reader.ml obj/MLS_Test_Types.cmx
obj/MLS_Test_Equality.cmx: obj/MLS_Test_Equality.ml

# Final binary

ALL_CMX_FILES=obj/MLS_Test_Reader.cmx obj/MLS_Test_Equality.cmx $(subst .ml,.cmx,$(ALL_ML_FILES))

bin/test.exe: obj/MLS_Test.cmx | bin
	$(OCAMLOPT) -I obj $(HACL_SNAPSHOT_DIR)/haclml/libhaclml.cmxa $(ALL_CMX_FILES) -o bin/test.exe

bin:
	mkdir $@

test: bin/test.exe test_vectors
	time $<

# Test vectors

test_vectors:
	mkdir -p test_vectors
	wget https://raw.githubusercontent.com/openmls/openmls/main/openmls/test_vectors/kat_treemath_openmls.json -O test_vectors/treemath.json
	wget https://raw.githubusercontent.com/openmls/openmls/main/openmls/test_vectors/kat_tree_kem_openmls.json -O test_vectors/treekem.json
	wget https://raw.githubusercontent.com/openmls/openmls/main/openmls/test_vectors/kat_key_schedule_openmls.json -O test_vectors/key_schedule.json
	wget https://raw.githubusercontent.com/openmls/openmls/main/openmls/test_vectors/kat_encryption_openmls.json -O test_vectors/encryption.json
	wget https://raw.githubusercontent.com/openmls/openmls/main/openmls/test_vectors/kat_transcripts.json -O test_vectors/commit_transcript.json

