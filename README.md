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
Suppose the target location is **11** line in **Main.java** file.
```sh
./unitcon build test/Main
./unitcon analyze test/Main --target Main.java:11
./unitcon synthesize test/Main --target Main.java:11
```

## Running Unitcon
If you want to make the data you need to run the Unitcon one by one, please follow it from here.

### Requirements
The structure of the target directory should follow the structure below.
```
target_dir
    |--...
    └--unitcon-properties
        |--build-command (for building and analyzing the target program)
        |--expected-bug (option)
        └--expected-bug-type (option)
```

All data needed for synthesis must be contained in the `unitcon-properties` directory within the target directory.

#### 1. build-command
`build-command` contains a sequence of commands required to build the target program.  
The following command is the contents of `test/Main`'s `build-command`.
```
 javac Main.java
```
Unitcon creates a single jar file by executing the build sequence of `build-command`. Therefore, Unitcon expects that all dependencies exist in the target directory.
If the target program uses a build system such as **Maven**, the `build-command` must contain the command such as `mvn dependency:copy-dependencies`.

#### 2. expected-bug & expected-bug-type
`expected-bug` and `expected-bug-type` may not be contained in the `unitcon-properties` if you do not need to synthesize a test case for specific error-triggering.  
If you have an expected error's trace and error's type, you can add the `expected-bug` and `expected-bug-type` files each like below.
- expected-bug: `at Main.toString(Main.java:11)`
- expected-bug-type: `java.lang.NullPointerException`

### Build
```sh
# Make a single jar file with the target program compiled
# and analyze the extra data for test case synthesis.
$ ./unitcon build PATH/TO/TARGET/DIR
```

### Analyze
```sh
# Analyze the target program.
$ ./unitcon analyze PATH/TO/TARGET/DIR --target [target location]
```
The form of target location should be `[file name]:[line number]`.
file name is a name that contains the full path from the target directory to a file.


### Synthesize
```sh
$ ./unitcon synthesize PATH/TO/TARGET/DIR --target [target location]
```
If Unitcon successfully synthesizes the `error-triggering test case`, the completed test case will be located in `unitcon-out/unitcon-tests`.
