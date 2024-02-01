{lib, stdenv, which, fstar, fstar-dune, z3, nodejs_20, ocamlPackages, comparse, dolev-yao-star, hacl-star-src, hacl-packages-src, fetchFromGitHub}:

let
  mls-star = stdenv.mkDerivation {
    name = "mls-star";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "hacl-star-snapshot"
        "hacl-star-snapshot/lib(/.*)?"
        "hacl-star-snapshot/specs(/.*)?"
        # Include all the F* files, except the ones in fstar/test
        # The directory fstar/test has to be created though, as it is hardcoded in the makefile
        "fstar"
        "fstar/test"
        "fstar/(api|common|glue|symbolic|treedem|treekem|treemath|treesync).*"
      ]
    ;
    enableParallelBuilding = true;
    buildInputs = [ which fstar z3 ];
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    installPhase = ''
      mkdir -p $out
      cp -r ml fstar cache hints $out
    '';
    passthru.tests = mls-star-tests;
    passthru.js = mls-star-js;
  };

  mls-star-tests = stdenv.mkDerivation {
    name = "mls-star-tests";
    src =
      lib.sources.sourceByRegex ./. [
        "hacl-star-snapshot(/.*)?"
        "fstar(/.*)?"
        "Makefile"
        "dune-project"
        "ml(/lib(/dune)?)?"
        "ml(/tests(/dune)?)?"
        "mls.opam"
        "test_vectors(/git_commit)?"
      ]
    ;
    enableParallelBuilding = true;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml dune_3 findlib yojson hacl-star
      ])
      ++ (fstar-dune.buildInputs);
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    # pre-patch uses build output from mls-star, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${mls-star}/cache ${mls-star}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
      mkdir -p test_vectors/data
      cp -pr --no-preserve=mode ${test-files}/test-vectors/* test_vectors/data
    '';
    doCheck = true;
    installPhase = ''
      mkdir -p $out
      cp -r ml fstar cache hints $out
    '';
    passthru.test-vectors = test-files;
  };

  test-rev = builtins.replaceStrings ["\n"] [""] (builtins.readFile ./test_vectors/git_commit);
  test-files =
    fetchFromGitHub {
      owner = "mlswg";
      repo = "mls-implementations";
      rev = test-rev;
      sha256 = "sha256-qYtSzY9epzvgahbJ3/omzGRwH5PVDLQmFfHzmQLDRc8=";
    }
  ;

  mls-star-js = stdenv.mkDerivation {
    name = "mls-star-js";
    src =
      lib.sources.sourceByRegex ./. [
        "hacl-star-snapshot(/.*)?"
        "fstar(/.*)?"
        "Makefile"
        "dune-project"
        "ml(/lib(/dune)?)?"
        "ml(/tests(/dune)?)?"
        "js(/.*)?"
        "mls.opam"
      ]
    ;
    enableParallelBuilding = true;
    # pre-patch uses build output from mls-star, to avoid building things twice
    prePatch = ''
      patchShebangs js/import.sh
      cp -pr --no-preserve=mode ${mls-star-tests}/cache ${mls-star-tests}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    buildPhase = ''
      make build
      (cd js; ./import.sh)
    '';
    doCheck = true;
    checkPhase = ''
      cd js
      node index.js
    '';
    installPhase = ''
      touch $out
    '';
    buildInputs =
      [ which fstar z3 nodejs_20 ]
      ++ (with ocamlPackages; [
        ocaml dune_3 findlib yojson hacl-star
        js_of_ocaml js_of_ocaml-ppx integers_stubs_js
      ])
      ++ (fstar-dune.buildInputs);
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    HACL_HOME = hacl-star-src;
    HACL_PACKAGES_HOME = hacl-packages-src;
  };

in
  mls-star
