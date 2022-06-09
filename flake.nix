{
  inputs = {
    nixpkgs.url = "nixpkgs";

    fstar-src = {
      url = "github:FStarLang/FStar";
      flake = false;
    };

    comparse_flake = {
      url = "git+ssh://git@github.com/TWal/comparse.git";
      inputs.fstar-src.follows = "fstar-src";
    };

    everest = {
      url = github:project-everest/everest-nix?dir=projects;
      inputs.fstar-src.follows = "fstar-src";
    };
  };

  outputs = {self, nixpkgs, fstar-src, comparse_flake, everest}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = everest.packages.${system}.z3;
    fstar = everest.packages.${system}.fstar;
    comparse = comparse_flake.packages.${system}.comparse;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar z3 comparse; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;};
  in {
    packages.${system} = {
      inherit fstar mls-star;
    };
    defaultPackage.${system} = mls-star;
    hydraJobs = {
      mls-build.${system} = mls-star;
      mls-tests.${system} = mls-star.tests;
    };
  };
}
