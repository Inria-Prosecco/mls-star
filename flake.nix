{
  inputs = {
    nixpkgs.url = "nixpkgs";

    fstar-src = {
      url = "github:FStarLang/FStar";
      flake = false;
    };

    everest = {
      url = github:project-everest/everest-nix?dir=projects;
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-src.follows = "fstar-src";
    };

    comparse-flake = {
      url = "git+ssh://git@github.com/TWal/comparse.git";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-src.follows = "fstar-src";
      inputs.everest.follows = "everest";
    };

    dolev-yao-star-src = {
      url = "git+ssh://git@github.com/prosecco/dolev-yao-star.git";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-src, everest, comparse-flake, dolev-yao-star-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = everest.packages.${system}.z3;
    fstar = everest.packages.${system}.fstar;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-src;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar z3 comparse dolev-yao-star; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;};
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
