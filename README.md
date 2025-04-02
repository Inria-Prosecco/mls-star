# mls-star

A formal specification of IETF MLS in F\*

## Papers linked to this repository

- TreeSync: Authenticated Group Management for Messaging Layer Security, USENIX Security '23 ([usenix](https://www.usenix.org/conference/usenixsecurity23/presentation/wallez)) ([eprint](https://eprint.iacr.org/2022/1732))
- TreeKEM: A Modular Machine-Checked Symbolic Security Analysis of Group Key Agreement in Messaging Layer Security, ([eprint](https://eprint.iacr.org/2025/410))

## What is verified?

Currently, we prove security properties on the sub-protocols TreeSync and TreeKEM.
TreeDEM is not yet verified.

## How to build

### The easy way

Using the Nix package manager:
- to obtain a shell with all the dependencies installed, run `nix develop`
- MLS\* and run all its tests, run `nix flake check`
- to compile MLS\* to Javascript, run `nix build .#mls-star.js`

The next sections are devoted on how to setup MLS\* without Nix.

### Dependencies

MLS\* depends on the F\* proof-oriented programming language and the Z3 SMT solver,
as well as two libraries:
- [Comparse](https://github.com/TWal/comparse), for message formatting
- [DY\*](https://github.com/REPROSEC/dolev-yao-star-extrinsic), for symbolic security proofs

The Javascript extraction of MLS\* furthermore rely on:
- [HACL Packages](https://github.com/cryspen/hacl-packages), for the WASM build of HACL\* and its Javascript wrapper

### Installing F\*

We use bleeding edge features of F\*, hence we recommend to use the latest commit of F\*'s master branch.

MLS\* is actively maintained (at the time of writing) and will be updated quickly in case a new version of F\* breaks the build,
however if this is not the case anymore,
you can find the commit of F\* that was used for CI tests (hence should be compatible) with the following command:
`jq -r '.nodes."fstar-flake".locked.rev' flake.lock`

To actually see how to install F\*, we refer to the instructions in the F\* repository.

The following commands should setup F\*.

```bash
git clone git@github.com:FStarLang/FStar.git
cd FStar
# omitting the next command is probably fine, if you feel lucky
git checkout $(jq -r '.nodes."fstar-flake".locked.rev' path/to/mls-star/flake.lock)
# install F* dependencies with opam, see F*'s INSTALL.md
make -j
export FSTAR_EXE=$(pwd)/bin/fstar.exe
# obtain Z3 4.8.5 here https://github.com/FStarLang/binaries/tree/master/z3-tested
export PATH=$PATH:$(cd directory/where/z3/4.8.5/lives; pwd)
# alternatively use the get_fstar_z3.sh script in the F* repo
```

### Installing Comparse and DY\*

Two choices are possible:
- either [Comparse](https://github.com/TWal/comparse) is cloned in `../comparse`,
  [DY\*](https://github.com/REPROSEC/dolev-yao-star-extrinsic) is cloned in `../dolev-yao-star`,
  and `fstar.exe` is in the `PATH`
- or [Comparse](https://github.com/TWal/comparse) is cloned in `COMPARSE_HOME`,
  [DY\*](https://github.com/REPROSEC/dolev-yao-star-extrinsic) is cloned in `DY_HOME`,
  and `FSTAR_EXE` is set to the location of `fstar.exe`,
  in that case using [direnv](https://direnv.net/) is a advisable.

When using relative path, the following commands will setup the dependencies.

```bash
cd ..
git clone git@github.com:TWal/comparse.git
git clone git@github.com:REPROSEC/dolev-yao-star-extrinsic.git dolev-yao-star
```

When using environement variables, the following commands will setup the dependencies.

```bash
git clone git@github.com:TWal/comparse.git
export COMPARSE_HOME=$(cd comparse; pwd)
git clone git@github.com:REPROSEC/dolev-yao-star-extrinsic.git dolev-yao-star
export DY_HOME=$(cd dolev-yao-star; pwd)
```

### Installing the OCaml dependencies

MLS\* compiles with OCaml, you must use the same version as the one used to compile F\*.
See F\*'s INSTALL.md file.

The OCaml extraction rely on the following opam packages:

```bash
opam install ocamlfind yojson hacl-star
```

The Javascript extraction furthermore rely on the following opam packages:

```bash
opam install js_of_ocaml js_of_ocaml-ppx integers_stubs_js
```

### Installing HACL Packages (for the Javascript build)

- [HACL Packages](https://github.com/cryspen/hacl-packages), must be cloned in `HACL_PACKAGES_HOME`

```bash
git clone git@github.com:cryspen/hacl-packages.git
export HACL_PACKAGES_HOME=$(cd hacl-packages; pwd)
```

### Building

- `make` will verify MLS\*
- `make check` will run the tests of MLS\* (interoperability tests, and some light fuzzing)
- `make js` will compile MLS\* to Javascript
- `node js/test.js` will start the Javascript tests

Some parts of the verification can be omitted if just the extracted code is useful:
- `NO_DY=1 make ...` will omit all the symbolic security proofs verification (hence do not require DY\* as a dependency)
- `ADMIT=1 make ...` will admit all SMT queries
