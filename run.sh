#!/bin/bash

INFER_BIN=~/unittest-infer/infer/bin/infer
cd test
$INFER_BIN capture -- javac Main.java
$INFER_BIN analyze --biabduction-only
$INFER_BIN debug --procedures --procedures-summary-json > infer-out/summary.json
cd ..

TRACE=test/infer-out/report.json
ERROR_SUMMARY=test/infer-out/error_summarys
SUMMARY=test/infer-out/summary.json

python3 error_summary_parser.py $ERROR_SUMMARY
ERROR_SUMMARY=$ERROR_SUMMARY.json

./unitgen $TRACE $ERROR_SUMMARY $SUMMARY