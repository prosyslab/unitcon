<img src="https://github.com/prosyslab/unitcon/assets/44044134/80ea91bc-8d08-462a-b8c1-d25edb761349"  width="140">

# Unitcon

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
python3 script/inheritance_info_parser.py PATH/TO/SOURCE/DIR  [ utf-8 | iso-8859-1 ]
python3 script/enum_parser.py PATH/TO/SOURCE/DIR  [ utf-8 | iso-8859-1 ]
cp PATH/TO/SOURCE/DIR/hierarchy_info.json PATH/TO/SOURCE/DIR/infer-out/inheritance_info.json
cp PATH/TO/SOURCE/DIR/hierarchy_info.json PATH/TO/SOURCE/DIR/infer-out/enum_info.json
cp -r PATH/TO/SOURCE/DIR/infer-out unitcon/test
```

## Run
```sh
./unitgen test
```
