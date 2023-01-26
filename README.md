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

## Run
```
./unitgen test/summary.json test/error-summary.json test/trace.json
```

## Visualize a Callgraph
```
./unitgen -print-callgraph test/example1.json
dot -Tpng -o example1.png unitgen-out/callgraph.dot
```
