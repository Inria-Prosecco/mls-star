# Building MLS\*

## OCaml

- Make sure you have `dune` installed (`opam install dune`), then run `make`.
- To run the tests, run `make test`.

It is *no longer* possible to run the test executable via the old build targets
in `new/`. Dune now builds everything, including the HACL\* OCaml snapshot, the
OCaml-extracted MLS library, the test files & test executable, as well as the new JS
build.

## JS

- Switch to F\* branch `protz_linkpkg`, remove `FStar/bin/fstarlib`, then in
  `ulib` run `make -j install-fstarlib`.
- Run `make` as usual in this directory.
- Open `js/index.html` and you should see some output in the developer console
  if you call `debug()`.
