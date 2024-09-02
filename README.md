<img src="https://github.com/prosyslab/unitcon/assets/44044134/80ea91bc-8d08-462a-b8c1-d25edb761349"  width="140">

# Unitcon

## Build
```
$ ./setup.sh
```

## Activate Python virtual environment
```sh
$ source venv/bin/activate
```

## Prerequisites
```sh
$ python3 script/enum_parser.py PATH/TO/SOURCE/DIR --encoding  [ utf-8 | iso-8859-1 ]
$ python3 script/constant_collector.py PATH/TO/SOURCE/DIR --encoding  [ utf-8 | iso-8859-1 ]
$ python3 script/command_maker.py PATH/TO/SOURCE/DIR
$ ./unitcon PATH/TO/SOURCE/DIR -class-info
```
Additionally, the source directory must contains static analysis results within the `unitcon_properties` directory.

## Run
```sh
$ ./unitcon PATH/TO/SOURCE/DIR
```
