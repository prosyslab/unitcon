#!/bin/bash
set -e
export OPAMYES=1

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
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

git submodule init
git submodule update
if [ ! -d "venv" ]; then
  python3 -m venv venv
fi
source venv/bin/activate
pip3 install -r requirements.txt

if [ ! -d "build" ]; then
  mkdir build
fi

eval $(SHELL=bash opam config env --switch=$UNITCON_OPAM_SWITCH)
opam pin add git+https://github.com/prosyslab/logger.git
opam install -j $NCPU dune ocamlgraph yojson ppx_compare z3 core logger
opam upgrade dune
make
