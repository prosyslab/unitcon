<img src="https://github.com/prosyslab/unitcon/assets/44044134/80ea91bc-8d08-462a-b8c1-d25edb761349"  width="140">

# Unitcon

## Dependencies
- Java 8

## Build
```
$ ./setup.sh
```

## Prerequisites
```sh
# Make a jar file with the target program compiled.
$ python3 script/command_maker.py PATH/TO/TARGET/DIR

# Analyze the target program.
$ cd PATH/TO/TARGET/DIR
$ PATH/TO/INFER capture -- [build command]
$ PATH/TO/INFER analyze --pulse-only --show-latent
$ PATH/TO/INFER debug --procedures --procedures-summary-json > infer-out/summary.json

# Analyze the extra information for test case synthesis.
$ ./unitcon PATH/TO/TARGET/DIR -class-info
$ ./unitcon PATH/TO/TARGET/DIR -constant-info
```
All data needed for synthesis must be contained in the `unitcon_properties` directory within the target directory.
```
target_dir
    |--with_dependency.jar
    └--unitcon_properties
        |--error_summaries.json (static analysis result)
        |--call_proposition.json (static analysis result)
        |--summary.json (static analysis result)
        |--build_command (for making with_dependency.jar)
        |--class_info.json
        |--constant_info.json
        |--expected_bug (option)
        └--expected_bug_type (option)
```

## Synthesize
```sh
$ ./unitcon PATH/TO/TARGET/DIR
```
If Unitcon successfully synthesizes the `error-triggering test case`, the completed test case will be located in `PATH/TO/TARGET/DIR/unitcon_tests`.

## Example
You can run UnitCon on the `Bears-189-buggy` program inside the `test` directory by executing the following command.  
The executable files for `Java` and `Maven` required for running the example have been included in the `test` directory.
```sh
./run.sh
```
