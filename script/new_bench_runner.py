"""Runs Unitcon on a new benchmark"""
import argparse
import pathlib
import os
import shutil
import subprocess
import datetime


VERBOSE: bool = False


######################################################
#             Debugging helper functions             #
######################################################


def debug(msg: str) -> None:
    """Prints a debug message only when verbose option is set.

    :param msg: Debug message
    """
    if VERBOSE:
        print("[debug] " + msg)


def run_with_debug(cmd: str, *args, **kwargs) -> None:
    """Runs a subprocess using the given command and arguments.
    If verbose option is set, prints the output.

    :param cmd: Command to execute
    """
    debug(f"Running command: {cmd.strip()}")
    debug(f"{args=}")
    debug(f"{kwargs=}")
    output: str = subprocess.run(
        cmd, *args, **kwargs, capture_output=True, check=False
    ).stdout.decode("utf-8")
    debug(f"Output:\n{output}")


def print_curr_time() -> None:
    """Prints the current time for debugging purposes.
    Only when verbose option is set.
    """

    if VERBOSE:
        debug(datetime.datetime.now().strftime("%m/%d %H:%M:%S"))


######################################################
#                Infer analysis step                 #
######################################################


def execute_build_cmd(project_dir: str, infer_path: str, version: int) -> None:
    """Perform `infer capture` on the target project.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    :param version: Java version of the target project
    """
    debug(f"Executing build cmd: {project_dir=} {infer_path=}")
    build_cmd_file: str = os.path.join(
        project_dir, "unitcon_properties", "unitcon_build_command"
    )
    assert os.path.isfile(build_cmd_file), f"Failed to build {project_dir}"

    with open(build_cmd_file, "r", encoding="utf-8") as f:
        for cmd in f.readlines():
            if cmd.startswith("mvn dependency"):
                continue
            if cmd.startswith("mvn clean"):
                cmd = " ".join(
                    [infer_path, "capture", "--java-version", str(version), "--", cmd]
                )
                run_with_debug(cmd, cwd=project_dir, shell=True)
            else:
                run_with_debug(cmd, cwd=project_dir, shell=True)


def execute_analyzer(project_dir: str, infer_path: str) -> None:
    """Perform `infer analyze` on the target project.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    """
    debug("Executing analyzer...")
    cmd: str = " ".join([infer_path, "analyze", "--pulse-only", "--show-latent"])
    run_with_debug(cmd, cwd=project_dir, shell=True)


def execute_summary_maker(project_dir: str, infer_path: str) -> None:
    """Perform `infer debug` on the target project to create error summaries.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    """
    debug("Executing summary maker...")
    summary_file: str = os.path.join(project_dir, "infer-out", "summary.json")
    cmd: str = " ".join(
        [infer_path, "debug", "--procedures", "--procedures-summary-json"]
    )

    debug(f"Running command: {cmd}")
    debug("args=()")
    debug("kwargs={{'cwd': 'project_dir', 'shell': True}}")
    result: bytes = subprocess.run(
        cmd, cwd=project_dir, shell=True, capture_output=True, check=False
    ).stdout
    with open(summary_file, "wb") as f:
        debug(f"Writing result to {summary_file}...")
        f.write(result)


def mk_error_summary_file(dirpath: str, error_count: int, buf: str) -> None:
    """Save the provided error summary to a `.json` file.

    :param dirpath: Directory in which to save the file
    :param error_count: Unique integer to enumerate each error summary
    :param buf: Error summary string
    """
    debug("Making error summary file...")

    file_path: str = os.path.join(dirpath, str(error_count) + ".json")
    debug(f"{file_path=}")
    with open(file_path, "w", encoding="utf-8") as f:
        f.write(buf)


def split_error_summary(dirpath: str, summary: str) -> None:
    """Extract relevant data from the error summary, and save them to `.json` files.

    :param dirpath: Directory in which to save the error summaries
    :param summary: Path to the `.json` file that contains the entire error summary
    """
    debug(f"Splitting error summary: {dirpath=} {summary=}")
    src_lines: list[str] = []  # All lines of the error summary
    buf: str = ""  # Saves the current line of the error summary
    error_count: int = 0  # Determines the name of the .json file

    with open(summary, "r", encoding="utf-8") as f:
        src_lines = f.readlines()
        debug(f"{src_lines=}")

    for i in src_lines:
        # debug(f"Current line: {i}")
        if '"Procname"' in i and '"BoItv"' in i:
            buf = i
            mk_error_summary_file(dirpath, error_count, buf)
            error_count += 1
            buf = ""
        elif '"BoItv"' in i:
            buf += i
            mk_error_summary_file(dirpath, error_count, buf)
            error_count += 1
            buf = ""
        else:
            buf += i


def split_error_summarys(project_dir: str) -> None:
    """Wrapper function for `split_error_summary()`.
    Creates the directory to save the individual error summary files.

    :param project_dir: Main directory path of the target project
    """
    debug("Splitting error summary...")
    err_summary: str = os.path.join(project_dir, "error_summarys.json")
    summarys_dir: str = os.path.join(project_dir, "error_summarys")

    if os.path.isdir(summarys_dir):
        debug(f"{summarys_dir} already exists. Removing...")
        shutil.rmtree(summarys_dir)

    debug(f"Making directory: {summarys_dir}")
    os.mkdir(summarys_dir)
    split_error_summary(summarys_dir, err_summary)


def copy_summary(project_dir: str) -> None:
    """Copy Infer's error summary into `unitcon_properties` file.
    After performing `split_error_summarys()`, copies the following directory and files:
    - `error_summarys`
    - `summary.json`
    - `call_proposition.json`

    :param project_dir: Main directory path of the target project
    """
    debug("Copying summary...")
    org_path: str = os.path.join(project_dir, "infer-out")
    new_path: str = os.path.join(project_dir, "unitcon_properties")

    if os.path.isfile(os.path.join(org_path, "summary.json")):
        debug(f"Copying file {org_path} to {new_path}")
        if os.path.isdir(os.path.join(new_path, "error_summarys")):
            debug(
                f"{os.path.join(new_path, 'error_summarys')} already exists. Removing..."
            )
            shutil.rmtree(os.path.join(new_path, "error_summarys"))
        split_error_summarys(org_path)

        debug(f"Copying relevant summarys from {org_path} to {new_path}...")
        debug("error_summarys")
        shutil.copytree(
            os.path.join(org_path, "error_summarys"),
            os.path.join(new_path, "error_summarys"),
        )

        debug("summary.json")
        shutil.copyfile(
            os.path.join(org_path, "summary.json"),
            os.path.join(new_path, "summary.json"),
        )

        debug("call_proposition.json")
        shutil.copyfile(
            os.path.join(org_path, "call_proposition.json"),
            os.path.join(new_path, "call_proposition.json"),
        )
    else:
        print(f"Failed to build {project_dir}")


def run_infer(project_dir: str, infer_path: str, version: int) -> None:
    """Wrapper function for Infer analysis and summarizing the results for Unitcon.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    :param version: Java version of the target project
    """
    debug("Running infer...")
    execute_build_cmd(project_dir, infer_path, version)
    execute_analyzer(project_dir, infer_path)
    execute_summary_maker(project_dir, infer_path)
    copy_summary(project_dir)


######################################################
#               Unicon preprocessing                 #
######################################################


def run_parser(project_dir: str, encoding: str) -> None:
    """Wrapper function for Unitcon preprocessing procedures.
    Executes the following scripts:
    - `constant_collector.py`
    - `enum_parser.py`
    - `inheritance_info_parser.py`

    :param project_dir: Main directory path of the target project
    :param encoding: Encoding of the target project source files
    """
    debug("Running parser...")
    script_list: list[str] = [
        "constant_collector.py",
        "enum_parser.py",
        "inheritance_info_parser.py",
    ]
    for script in script_list:
        cmd: str = " ".join(
            [
                "source",
                "venv/bin/activate;",  # Activate the virtual environment required for preprocessing
                "python3",
                os.path.join("script", script),
                project_dir,
                "--encoding",
                encoding,
            ]
        )
        debug(f"Running command: {cmd}")
        os.system("bash -c " + '"' + cmd + '"')


def run_command_maker(project_dir: str, build_type: str) -> None:
    """Wrapper function for Unitcon command maker script (`comand_maker.py`).

    :param project_dir: Main directory path of the target project
    :param build_type: Compile method of the project. (\"maven\" / \"javac\")"""
    debug("Running cmd maker...")
    cmd: str = " ".join(
        ["python3", os.path.join("script", "command_maker.py"), project_dir, build_type]
    )
    run_with_debug(cmd, cwd=os.getcwd(), shell=True)


######################################################
#               Unicon main program                  #
######################################################


def copy_error_summary(project_dir: str, error_count: int) -> bool:
    """Copies the denoted error summary to unitcon_properties directory.

    :param project_dir: Main directory path of the target project
    :param error_count: Number of the error summary file to copy
    :return: Success or failure of the copying procedure"""
    debug("Copying error summary...")
    prop_dir = os.path.join(project_dir, "unitcon_properties")

    # Remove error_summary used previously
    if os.path.isfile(os.path.join(prop_dir, "error_summarys.json")):
        debug(
            f"{os.path.join(prop_dir, 'error_summarys.json')} already exists. Deleting..."
        )
        os.remove(os.path.join(prop_dir, "error_summarys.json"))

    file_name: str = os.path.join(
        prop_dir, "error_summarys", str(error_count) + ".json"
    )
    if os.path.isfile(file_name):
        debug(
            f"{file_name} exists. Copying it to {os.path.join(prop_dir, 'error_summarys.json')}..."
        )
        shutil.copyfile(
            file_name,
            os.path.join(prop_dir, "error_summarys.json"),
        )
        return True
    debug(f"{file_name} does not exist!")
    return False


def run_unitcon(project_dir: str, unitcon_path: str) -> None:
    """Wrapper function for main Unitcon sequence.
    Iterate over each error summary file to run Unitcon and save the results.

    :param project_dir: Main directory path of the target project
    :param unitcon_path: Path of the unitcon executable
    """
    debug("Running unitcon...")
    error_count: int = 0
    all_results_dir: str = os.path.join(os.getcwd(), "results")
    result_dir: str = os.path.join(
        all_results_dir, os.path.basename(project_dir) + "-result"
    )

    if not os.path.isdir(all_results_dir):
        debug(f"{all_results_dir} does not exits. Creating...")
        os.mkdir(all_results_dir)
    elif os.path.isdir(result_dir):
        debug(f"{result_dir} already exists. Deleting...")
        shutil.rmtree(result_dir)
    debug(f"Creating directory {result_dir}...")
    os.mkdir(result_dir)

    while copy_error_summary(project_dir, error_count):
        result_file: str = os.path.join(result_dir, "result-" + str(error_count))
        cmd: str = " ".join([unitcon_path, project_dir, "-until-time-out"])

        print_curr_time()
        debug(f"Running command: {cmd}")
        debug("args=()")
        debug(
            f"kwargs={{'cwd': {os.getcwd()}, 'shell': True, 'stdout': {subprocess.PIPE}, 'universal_newlines': True}}"
        )
        process: subprocess.Popen = subprocess.Popen(
            cmd,
            cwd=os.getcwd(),
            shell=True,
            stdout=subprocess.PIPE,
            universal_newlines=True,
        )
        # Wait for ending of UnitCon
        process.wait()

        debug("Unitcon ended!")
        out, _ = process.communicate()
        with open(result_file, "wb") as f:
            debug(f"Writing results to {result_file}...")
            f.write(bytes(out, encoding="utf-8"))
        error_count += 1


######################################################
#                   Main Function                    #
######################################################


def main() -> None:
    """Executes the entire Unitcon workflow on the provided target project.

    Workflow:
    ```
    `- main()
       |- run_infer()
       |  |- execute_build_cmd()
       |  |- execute_analyzer()
       |  |- execute_summary_maker()
       |  `- copy_summary()
       |- run_parser()
       |- run_command_maker()
       `- run_unitcon()
    ```
    """
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "project",
        type=pathlib.Path,
        default=None,
        help="Project directory where need to execute UnitCon",
    )
    parser.add_argument(
        "--infer_path",
        type=pathlib.Path,
        default="/infer/infer/bin/infer",
        help="Path of infer's executable file",
    )
    parser.add_argument(
        "--unitcon_path",
        type=pathlib.Path,
        default="unitcon",  # Assumes `unitcon` is on PATH
        help="Path of unitcon's executable file",
    )
    parser.add_argument(
        "--encoding", type=str, default="utf-8", help="Encoding type of project"
    )
    parser.add_argument(
        "--build_type", type=str, default="maven", help="[maven | javac]"
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="Print debug lines"
    )
    parser.add_argument(
        "--version", type=int, default=8, help="Version of Java used in the project"
    )
    args = parser.parse_args()
    abspath = os.path.abspath(args.project)

    global VERBOSE
    VERBOSE = args.verbose

    run_infer(abspath, str(args.infer_path), args.version)
    run_parser(abspath, args.encoding)
    run_command_maker(abspath, args.build_type)
    run_unitcon(abspath, str(args.unitcon_path))


if __name__ == "__main__":
    main()
