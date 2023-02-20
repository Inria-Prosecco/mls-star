{lib, stdenv, which, fstar, z3, ocamlPackages, comparse, dolev-yao-star, fetchFromGitHub}:

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
    FSTAR_HOME = fstar;
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    installPhase = ''
      mkdir -p $out
      cp -r ml fstar cache hints $out
    '';
    passthru.tests = mls-star-tests;
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
      ++ (fstar.buildInputs);
    FSTAR_HOME = fstar;
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
      touch $out
    '';
    passthru.test-vectors = test-files;
  };

  test-rev = builtins.replaceStrings ["\n"] [""] (builtins.readFile ./test_vectors/git_commit);
  test-files =
    fetchFromGitHub {
      owner = "mlswg";
      repo = "mls-implementations";
      rev = test-rev;
      sha256 = "sha256-1QmaD5KVlxA6bJ0WHO1FDhykLHe3keVhtQUP1dH3Mgk=";
    }
  ;
in
  mls-star
