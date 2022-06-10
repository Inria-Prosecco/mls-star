{stdenv, which, fstar, z3, ocamlPackages, comparse}:

let
  mls-star = stdenv.mkDerivation {
    name = "mls-star";
    src = ./.;
    enableParallelBuilding = true;
    buildInputs = [ which fstar z3 ];
    FSTAR_HOME = fstar;
    COMPARSE_HOME = comparse;
    installPhase = ''
      mkdir -p $out
      cp -r ml fstar cache hints $out
    '';
    passthru.tests = mls-star-tests;
  };
  mls-star-tests = stdenv.mkDerivation {
    name = "mls-star-tests";
    src = ./.;
    enableParallelBuilding = true;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml dune_2 findlib
        # fstarlib dependencies
        batteries stdint zarith ppx_deriving_yojson
      ]);
    FSTAR_HOME = fstar;
    COMPARSE_HOME = comparse;
    # pre-patch uses build output from mls-star, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${mls-star}/cache ${mls-star}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    doCheck = true;
    installPhase = ''
      touch $out
    '';
  };
in
  mls-star