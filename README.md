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
mv PATH/TO/SOURCE/DIR/hierarchy_info.json PATH/TO/SOURCE/DIR/unitcon_properties/inheritance_info.json
mv PATH/TO/SOURCE/DIR/hierarchy_info.json PATH/TO/SOURCE/DIR/unitcon_properties/enum_info.json
```

## Run
```sh
./unitcon PATH/TO/SOURCE/DIR
```
