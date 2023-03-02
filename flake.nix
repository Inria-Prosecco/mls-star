{
  inputs = {
    nixpkgs.url = "nixpkgs";

    fstar-flake = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    comparse-flake = {
      url = "git+ssh://git@github.com/TWal/comparse.git";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
    };

    dolev-yao-star-src = {
      url = "git+ssh://git@github.com/prosecco/dolev-yao-star.git?ref=comparse";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-src;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar fstar-dune z3 comparse dolev-yao-star; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
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
    defaultPackage.${system} = mls-star;
    hydraJobs = {
      mls-build.${system} = mls-star;
      mls-tests.${system} = mls-star.tests;
    };
  };
}
