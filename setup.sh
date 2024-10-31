#!/bin/bash
set -e
export OPAMYES=1

OCAML_VERSION="4.14.0"
UNITCON_OPAM_SWITCH=unitcon-"$OCAML_VERSION"+flambda
JUNIT_FILE="deps/junit-4.13.2.jar"
HAMCREST_FILE="deps/hamcrest-core-1.3.jar"
MODE="$1"

build_infer () {
  git submodule init
  git submodule update
  cd unitcon-infer && ./build-infer.sh java
  cd ..
}

build_unitcon () {
  NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
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

  eval $(SHELL=bash opam env --switch=$UNITCON_OPAM_SWITCH)
  opam pin add git+https://github.com/prosyslab/logger.git
  opam install -j $NCPU dune ocamlgraph ppx_compare z3 core logger ounit bisect_ppx sawja
  opam install yojson.2.2.2
  opam install ocamlformat.0.26.1
  opam upgrade dune
  make
}

if [ ! -e $JUNIT_FILE ]; then
  wget https://repo1.maven.org/maven2/junit/junit/4.13.2/junit-4.13.2.jar -P deps/
fi
if [ ! -e $HAMCREST_FILE ]; then
  wget https://repo1.maven.org/maven2/org/hamcrest/hamcrest-core/1.3/hamcrest-core-1.3.jar -P deps/
fi

if [[ "$MODE" == "all" || "$MODE" == "" ]]; then
  build_unitcon
  build_infer
elif [[ "$MODE" == "infer" ]]; then
  build_infer
elif [[ "$MODE" == "unitcon" ]]; then
  build_unitcon
else
  echo "Not supported build mode: $MODE."
  echo "Supported build modes: [ all | infer | unitcon ]"
  exit 1
fi
