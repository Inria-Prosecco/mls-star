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
      url = "github:Inria-Prosecco/treesync";
      flake = false;
    };

    hacl-packages-src = {
      url = "github:cryspen/hacl-packages";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-src, hacl-packages-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = comparse-flake.packages.${system}.comparse;
    # The following is a hack, because nix is not able to fetch a subdirectory of a git repository
    # (there is the "?dir=..." syntax, but it works only to point to the flake.nix!)
    # There are two repositories where we may obtain dolev-yao-star
    # - from the private dolev-yao-star repository
    # - from the artifact of the TreeSync paper, that contains a recent public version of DY* in the dolev-yao-star subdirectory
    # Hence, this little condition will check whether there exists a "dolev-yao-star" subdirectory
    # (which only happens when dolev-yao-star-src points to the TreeSync artifact),
    # and go into it when that is the case.
    dolev-yao-star =
      if (builtins.readDir dolev-yao-star-src)?"dolev-yao-star" then
        "${dolev-yao-star-src}/dolev-yao-star"
      else
        dolev-yao-star-src
    ;
    mls-star = pkgs.callPackage ./default.nix {inherit fstar fstar-dune z3 comparse dolev-yao-star hacl-packages-src; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
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
      ++ (fstar-dune.buildInputs);
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
