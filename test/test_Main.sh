#!/bin/bash

# opam
UNITCON_OPAM_SWITCH=unitcon-4.14.0+flambda
INFER_OPAM_SWITCH=4.14.0+flambda

# Start at test directory
UNITCON_PATH=$(dirname $(pwd))
UNITCON_BIN=$UNITCON_PATH/unitcon
if [ "$1" == "-make-test" ]; then
  INFER_BIN=$(dirname $(dirname $(dirname $(pwd))))/unitcon-infer/infer/bin/infer
else
  INFER_BIN=$UNITCON_PATH/unitcon-infer/infer/bin/infer
fi
PROJECT=$UNITCON_PATH/test/Main

# make dependencies.jar
python3 $UNITCON_PATH/script/command_maker.py $PROJECT
cd $PROJECT

# infer-build
eval $(SHELL=bash opam switch $INFER_OPAM_SWITCH)

while IFS= read -r cmd; do
  $INFER_BIN capture -- $cmd
done < "$PROJECT/unitcon_properties/build_command"

# analyze
$INFER_BIN analyze --pulse-only --show-latent

# extract summary
$INFER_BIN debug --procedures --procedures-summary-json > $PROJECT/infer-out/summary.json

# copy analysis result files to unitcon_properties directory
cp $PROJECT/infer-out/summary.json $PROJECT/unitcon_properties/summary.json
cp $PROJECT/infer-out/call_proposition.json $PROJECT/unitcon_properties/call_proposition.json
cd $UNITCON_PATH
eval $(SHELL=bash opam switch $UNITCON_OPAM_SWITCH)

$UNITCON_BIN $PROJECT -class-info
$UNITCON_BIN $PROJECT -constant-info

# synthesize test case
$UNITCON_BIN $PROJECT $PROJECT