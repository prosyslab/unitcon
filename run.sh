#!/bin/bash

# opam
UNITCON_OPAM_SWITCH=unitcon-4.14.0+flambda
INFER_OPAM_SWITCH=4.14.0+flambda

# Start at Unitcon directory
UNITCON_PATH=$(pwd)
INFER_BIN=$UNITCON_PATH/unitcon-infer/infer/bin/infer
PROJECT=$UNITCON_PATH/test/Bears-189-buggy

TRACE=test/source/report.json
ERROR_SUMMARY=test/source/error_summarys
SUMMARY=test/source/summary.json

source venv/bin/activate
python3 error_summary_parser.py $ERROR_SUMMARY
ERROR_SUMMARY=$ERROR_SUMMARY.json

cd $PROJECT
eval $(SHELL=bash opam switch $INFER_OPAM_SWITCH)

# infer-build
while IFS= read -r cmd; do
  if [[ $cmd == mvn\ dependency* ]]; then
    continue
  elif [[ $cmd == mvn\ clean* ]]; then
    $INFER_BIN capture --java-version 8 -- $cmd
  else
    $cmd
  fi
done < "unitcon_properties/build_command"

# analyze
SOURCE="src/main/java/hu/oe/nik/szfmv/detector/classes/Detector.java"
LINE=52
$INFER_BIN analyze --pulse-only --show-latent --target-file-name $SOURCE --target-file-line $LINE

# extract summary
$INFER_BIN debug --procedures --procedures-summary-json > infer-out/summary.json

# copy analysis result files to unitcon_properties directory
cp infer-out/summary.json unitcon_properties/summary.json
cp infer-out/call_proposition.json unitcon_properties/call_proposition.json

cd $UNITCON_PATH
eval $(SHELL=bash opam switch $UNITCON_OPAM_SWITCH)

./unitcon $PROJECT -class-info
./unitcon $PROJECT -constant-info

# synthesize test case
./unitcon $PROJECT
