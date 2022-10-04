# unitgen

## Build
```
./setup.sh
make
```

## Run
```
./unitgen test/null1.json test/summary1.json
```

## Visualize a Callgraph
```
./unitgen -print-callgraph test/example1.json
dot -Tpng -o example1.png unitgen-out/callgraph.dot
```
