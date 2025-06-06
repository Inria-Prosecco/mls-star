{
  inputs = {
    fstar-flake.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar-flake/nixpkgs";

    comparse-flake = {
      url = "github:TWal/comparse";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
    };

    dolev-yao-star-flake = {
      url = "github:REPROSEC/dolev-yao-star-extrinsic";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
      inputs.comparse-flake.follows = "comparse-flake";
    };

    hacl-packages-src = {
      url = "github:cryspen/hacl-packages";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-flake, hacl-packages-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-flake.packages.${system}.dolev-yao-star;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar z3 comparse dolev-yao-star hacl-packages-src; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
      default = mls-star;
      inherit mls-star;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
        ocaml dune_3 findlib yojson hacl-star
        js_of_ocaml js_of_ocaml-ppx integers_stubs_js
      ])
      ++ (fstar.buildInputs);
      COMPARSE_HOME = comparse;
      DY_HOME = dolev-yao-star;
      HACL_PACKAGES_HOME = hacl-packages-src;
    };
    checks.${system} = {
      mls-star-build = mls-star;
      mls-star-tests = mls-star.tests;
      mls-star-js = mls-star.js;
    };
  };
}
