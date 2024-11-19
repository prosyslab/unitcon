<img src="https://github.com/prosyslab/unitcon/assets/44044134/80ea91bc-8d08-462a-b8c1-d25edb761349"  width="140">

# Unitcon
Unitcon is a targeted unit test generator for Java.

## Dependencies
- Java 8
- Python 3

## Build Unitcon
```
$ ./setup.sh
```

## Runnin Unitcon on a Example Program
You can run Unitcon on the `Main` program inside the `test` directory by executing the following command.  
Suppose the target location is line **11** in [Main.java](test/Main/Main.java#L11).
```sh
./unitcon build test/Main
./unitcon analyze test/Main --target Main.java:11
./unitcon synthesize test/Main --target Main.java:11
```

## Running Unitcon on Your Project
If you want to run Unitcon on a new project, follow the instructions below.

### 1. Configuration
Create a directory named `unitcon-properties` under your project directory `target-dir`
and write configuration files.
The structure of the target directory will be as follows:
```
target-dir
  |--...
  └--unitcon-properties
    |--build-command (for building and analyzing the target program)
    |--expected-bug (optional)
    └--expected-bug-type (optional)
```
There are three configuration files:
* build-command (required): This file should contain a sequence of commands to build the target program. See the [example](test/Main/unitcon-properties/build-command).
  Unitcon creates a single jar file by executing the build sequence of `build-command`. Therefore, Unitcon expects that all dependencies exist in the target   directory. If the target program uses a build system such as **Maven**, the `build-command` must contain the command such as `mvn dependency:copy-dependencies`.

* expected-stack-trace (optional): If you want to detect an exception with a specific stack trace, provide the details such as `at Main.toString(Main.java:11)`. If the file is not provided, Unitcon considers only the final function call.
* expected-bug-type (optional): If you want to detect a specific type of exception at the target location, specify the full name of the exception such as `java.lang.NullPointerException`. If this file is not provided, Unitcon consider all exceptions at the target location.
`expected-bug` and `expected-bug-type` may not be contained in the `unitcon-properties` if you do not need to synthesize a test case for specific error-triggering.  

### 2. Build
Build the target project for Unitcon with the following command.
The command makes a single jar file that contains all classes of the target project.
```sh
$ ./unitcon build PATH/TO/TARGET/DIR
```

### 3. Analyze
```sh
# Analyze the target program.
$ ./unitcon analyze PATH/TO/TARGET/DIR --target [file name]:[line number]
```
Note that `file name` should contains the full path from the target directory to a file.


### 4. Synthesize
```sh
$ ./unitcon synthesize PATH/TO/TARGET/DIR --target [target location]
```
If the unit tests have been created successfully, they will be inside the `unitcon-out/unitcon-tests` directory.
