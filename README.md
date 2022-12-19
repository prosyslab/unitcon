# unitgen

## Build
```
./setup.sh
make
```

## Run
```
./unitgen test/summary.json test/error-summary.json test/trace.json
```

## Visualize a Callgraph
```
./unitgen -print-callgraph test/example1.json
dot -Tpng -o example1.png unitgen-out/callgraph.dot
```
