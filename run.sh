#!/bin/bash

INFER_BIN=~/unittest-infer/infer/bin/infer
cd test
mkdir source
$INFER_BIN capture -- javac Main.java
$INFER_BIN analyze --biabduction-only
cp infer-out/report.json source/report.json
cp infer-out/error_summarys source/error_summarys
$INFER_BIN analyze --biabduction-only --find-missing-summary
$INFER_BIN debug --procedures --procedures-summary-json > source/summary.json
cd ..

TRACE=test/source/report.json
ERROR_SUMMARY=test/source/error_summarys
SUMMARY=test/source/summary.json

python3 error_summary_parser.py $ERROR_SUMMARY
ERROR_SUMMARY=$ERROR_SUMMARY.json

./unitgen $SUMMARY $ERROR_SUMMARY $TRACE