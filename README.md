<img src="https://github.com/prosyslab/unitcon/assets/44044134/80ea91bc-8d08-462a-b8c1-d25edb761349"  width="140">

# Unitcon

## Dependencies
- Java 8
- Python 3

## Build
```
$ ./setup.sh
```

## Example
You can run Unitcon on the `Main` program inside the `test` directory by executing the following command.
```sh
./unitcon build test/Main
./unitcon synthesize test/Main
```

## Obtain the required data before synthesis
If you want to make the data you need to run the Unitcon one by one, please follow it from here.

```sh
# Make a jar file with the target program compiled
# and analyze the extra data for test case synthesis.
$ ./unitcon build PATH/TO/TARGET/DIR

# Analyze the target program.
$ cd PATH/TO/TARGET/DIR
$ PATH/TO/INFER capture -- [build command]
$ PATH/TO/INFER analyze --pulse-only --show-latent --target-file-name [fname] --target-file-line [line]
$ PATH/TO/INFER debug --procedures --procedures-summary-json > infer-out/summary.json
```
All data needed for synthesis must be contained in the `unitcon-properties` directory within the target directory.  
But, `expected-bug` and `expected-bug-type` may not be contained in the `unitcon-properties` if you do not need to synthesize test case for target.
```
target_dir
    |--with-dependency.jar
    └--unitcon-properties
        |--build-command (for making with-dependency.jar)
        |--expected-bug (option)
        └--expected-bug-type (option)
```

## Synthesize
```sh
$ ./unitcon synthesize PATH/TO/TARGET/DIR
```
If Unitcon successfully synthesizes the `error-triggering test case`, the completed test case will be located in `unitcon-out/unitcon-tests`.
