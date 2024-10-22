#!/bin/bash
set -e
export OPAMYES=1

git submodule init
git submodule update
cd unitcon-infer && ./build-infer.sh java
make

cd ..
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.14.0"
UNITCON_OPAM_SWITCH=unitcon-"$OCAML_VERSION"+flambda
UNITCON_OPAM_SWITCH_OPTION="--package=ocaml-variants.${OCAML_VERSION}+options,ocaml-option-flambda"
opam init --reinit --bare -j $NCPU --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$UNITCON_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done

if [ "$switch_exists" = "no" ]; then
  opam switch create $UNITCON_OPAM_SWITCH_OPTION $UNITCON_OPAM_SWITCH
else
  opam switch $UNITCON_OPAM_SWITCH
fi

eval $(SHELL=bash opam config env --switch=$UNITCON_OPAM_SWITCH)
opam pin add git+https://github.com/prosyslab/logger.git
opam install -j $NCPU dune ocamlgraph yojson ppx_compare z3 core logger ounit bisect_ppx sawja
opam install ocamlformat.0.26.1
opam upgrade dune
make
