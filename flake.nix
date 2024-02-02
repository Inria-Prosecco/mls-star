{
  inputs = {
    fstar-flake.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar-flake/nixpkgs";

    comparse-flake = {
      url = "github:TWal/comparse";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
    };

    dolev-yao-star-src = {
      url = "github:prosecco/dolev-yao-star";
      flake = false;
    };

    hacl-star-src = {
      url = "github:hacl-star/hacl-star";
      flake = false;
    };

    hacl-packages-src = {
      url = "github:cryspen/hacl-packages";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-src, hacl-star-src, hacl-packages-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-src;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar fstar-dune z3 comparse dolev-yao-star hacl-star-src hacl-packages-src; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
      default = mls-star;
      inherit mls-star;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
        ocaml dune_3 findlib yojson
      ])
      ++ (fstar.buildInputs);
    };
    checks.${system} = {
      mls-star-build = mls-star;
      mls-star-tests = mls-star.tests;
      mls-star-js = mls-star.js;
    };
  };
}
