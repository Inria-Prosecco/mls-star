
This directory contains a self-contained snapshot of the HACL specs and libs for use in proofs and OCaml execution.


To verify your code against HACL:
Set HACL_HOME to this directory to add $(HACL_HOME)/lib and $(HACL_HOME)/specs to your FSTAR_INCLUDES.

To run your code in OCaml:
Run `make` in this directory to compile ml/libhaclml.cmxa
Add $(HACL_HOME)/ml/libhaclml.cmxa to your OCAMLOPT to command to link this library to your code.


