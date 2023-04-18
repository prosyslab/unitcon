# unitgen

## Build
```
./setup.sh
make
```

## Activate Python virtual environment
```sh
source venv/bin/activate
```

## Prerequisites
```sh
python3 script/hierarchy_info_parser.py PATH/TO/SOURCE/DIR  [ utf-8 | iso-8859-1 ]
cp PATH/TO/SOURCE/DIR/hierarchy_info.json PATH/TO/SOURCE/DIR/infer-out/hierarchy_info.json
cp -r PATH/TO/SOURCE/DIR/infer-out unitgen/test
```

## Run
```sh
python3 script/error_summary_parser.py test/error_summarys
python3 script/call_proposition_parser.py test/call_proposition
./unitgen test/summary.json test/error_summarys.json test/call_proposition.json test/hierarchy_info.json
```

## Visualize a Callgraph
```
./unitgen -print-callgraph test/example1.json
dot -Tpng -o example1.png unitgen-out/callgraph.dot
```
