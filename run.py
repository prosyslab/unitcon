"""Runs Unitcon on a new benchmark"""

import argparse
import pathlib
import os
import shutil
import subprocess
import datetime

VERBOSE: bool = False
CAPTURE_TO: float = 120.0
ANALYZE_TO: float = 120.0
PREPROCESS_TO: float = 120.0
UNITCON_TO: float = 1800.0

######################################################
#             Debugging helper functions             #
######################################################


class UnitconException(Exception):
    """Exception class for Unitcon"""


def debug(msg: str) -> None:
    """Prints a debug message only when verbose option is set.

    :param msg: Debug message
    """
    if VERBOSE:
        print("[debug] " + msg)


def run_with_debug(cmd: str, *args, timeout: float | None = None, **kwargs) -> None:
    """Runs a subprocess using the given command and arguments.
    If verbose option is set, prints the output.

    :param cmd: Command to execute
    :param timeout: Time limit for the subprocess in seconds (default: None)
    :raises UnitconException: If timeout expires
    """
    debug(f"Running command: {cmd.strip()}")
    debug(f"{args=}")
    debug(f"{kwargs=}")
    debug("")

    process: subprocess.Popen = subprocess.Popen(
        cmd,
        *args,
        **kwargs,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        universal_newlines=True,
    )

    try:
        while True:
            stdout_line: str | None = process.stdout.readline()
            stderr_line: str | None = process.stderr.readline()
            if not stdout_line and not stderr_line and process.poll() is not None:
                break
            if stdout_line:
                debug(stdout_line.strip())
            if stderr_line:
                debug(stderr_line.strip())

        process.wait(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        process.kill()
        raise UnitconException(f"Subprocess timeout expired (TO: {timeout})") from exc


def print_curr_time() -> None:
    """Prints the current time for debugging purposes.
    Only when verbose option is set.
    """

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

    build_cmd_file: str = os.path.join(project_dir, "unitcon_properties", "build_command")
    assert os.path.isfile(build_cmd_file), f"Failed to build {project_dir}"

    with open(build_cmd_file, "r", encoding="utf-8") as f:
        for cmd in f.readlines():
            if cmd.startswith("mvn dependency"):
                continue
            if cmd.startswith("mvn clean"):
                cmd = " ".join([infer_path, "capture", "--java-version", str(version), "--", cmd])
                run_with_debug(cmd, cwd=project_dir, shell=True, timeout=CAPTURE_TO)
            elif cmd.startswith("javac"):
                cmd = " ".join([infer_path, "capture", "--java-version", str(version), "--", cmd])
                run_with_debug(cmd, cwd=project_dir, shell=True, timeout=CAPTURE_TO)
            else:
                run_with_debug(cmd, cwd=project_dir, shell=True, timeout=PREPROCESS_TO)


def execute_analyzer(project_dir: str, infer_path: str) -> None:
    """Perform `infer analyze` on the target project.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    """
    debug("Executing analyzer...")
    cmd: str = " ".join([infer_path, "analyze", "--pulse-only", "--show-latent"])
    run_with_debug(cmd, cwd=project_dir, shell=True, timeout=ANALYZE_TO)


def execute_summary_maker(project_dir: str, infer_path: str) -> None:
    """Perform `infer debug` on the target project to create error summaries.

    :param project_dir: Main directory path of the target project
    :param infer_path: Path of the infer executable
    """
    debug("Executing summary maker...")
    summary_file: str = os.path.join(project_dir, "infer-out", "summary.json")
    cmd: str = " ".join([infer_path, "debug", "--procedures", "--procedures-summary-json"])

    debug(f"Running command: {cmd}")
    debug("args=()")
    debug("kwargs={{'cwd': 'project_dir', 'shell': True}}")
    result: bytes = subprocess.run(cmd,
                                   cwd=project_dir,
                                   shell=True,
                                   capture_output=True,
                                   check=False).stdout
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

    for i in src_lines:
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


def split_error_summaries(project_dir: str) -> None:
    """Wrapper function for `split_error_summary()`.
    Creates the directory to save the individual error summary files.

    :param project_dir: Main directory path of the target project
    """
    debug("Splitting error summary...")
    err_summary: str = os.path.join(project_dir, "error_summaries.json")
    summarys_dir: str = os.path.join(project_dir, "error_summaries")

    if os.path.isdir(summarys_dir):
        debug(f"{summarys_dir} already exists. Removing...")
        shutil.rmtree(summarys_dir)

    debug(f"Making directory: {summarys_dir}")
    os.mkdir(summarys_dir)
    split_error_summary(summarys_dir, err_summary)


def copy_summary(project_dir: str) -> None:
    """Copy Infer's error summary into `unitcon_properties` file.
    After performing `split_error_summaries()`, copies the following directory and files:
    - `error_summaries.json`
    - `summary.json`
    - `call_proposition.json`

    :param project_dir: Main directory path of the target project
    """
    debug("Copying summary...")
    org_path: str = os.path.join(project_dir, "infer-out")
    new_path: str = os.path.join(project_dir, "unitcon_properties")

    if not os.path.exists(new_path):
        os.makedirs(new_path)

    if os.path.isfile(os.path.join(org_path, "summary.json")):
        debug(f"Copying file {org_path} to {new_path}")
        if os.path.isdir(os.path.join(new_path, "error_summaries")):
            debug(f"{os.path.join(new_path, 'error_summaries')} already exists. Removing...")
            shutil.rmtree(os.path.join(new_path, "error_summaries"))
        split_error_summaries(org_path)

        debug(f"Copying relevant summarys from {org_path} to {new_path}...")
        debug("error_summaries")
        shutil.copytree(
            os.path.join(org_path, "error_summaries"),
            os.path.join(new_path, "error_summaries"),
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
    print_curr_time()
    debug("Running infer...")
    execute_build_cmd(project_dir, infer_path, version)
    execute_analyzer(project_dir, infer_path)
    execute_summary_maker(project_dir, infer_path)
    copy_summary(project_dir)


######################################################
#             Error summary filtering                #
######################################################


def file_content_hash(file_path: str) -> int:
    """Calculates the hash value of the provided file's content.

    :param file_path: Path to the error summary file
    """
    with open(file_path, "r") as f:
        return hash(f.read())


def remove_duplicate_summaries(project_dir: str) -> None:
    """Removes error summaries of identical contents.

    :param file_path: Main directory path of the target project
    """
    print_curr_time()
    debug("Checking for duplicate summaries...")
    hash_file_dict: dict[int, list[str]] = {}
    error_summary_dir: str = os.path.join(project_dir, "unitcon_properties", "error_summaries")
    for summary in os.listdir(error_summary_dir):
        if summary.endswith(".json"):
            summary_path: str = os.path.join(error_summary_dir, summary)
            hash_val: int = file_content_hash(summary_path)
            if hash_val in hash_file_dict:
                hash_file_dict[hash_val].append(summary_path)
            else:
                hash_file_dict.update({hash_val: [summary_path]})

    for possible_duplicates in hash_file_dict.values():
        cnt: int = len(possible_duplicates)
        if cnt > 1:
            duplicate: list[bool] = [False for _ in range(cnt)]
            for i in range(cnt - 1):
                for j in range(i + 1, cnt):
                    if not duplicate[i] and not duplicate[j]:
                        with open(possible_duplicates[i], "r") as f:
                            contents1: str = f.read()
                        with open(possible_duplicates[j], "r") as f:
                            contents2: str = f.read()
                        if contents1 == contents2:
                            debug(
                                f"Summary {possible_duplicates[j]} is a duplicate of summary {possible_duplicates[i]}!"
                            )
                            duplicate[j] = True

            for idx in range(cnt):
                if duplicate[idx]:
                    debug(f"Removing file {possible_duplicates[idx]}...")
                    os.remove(possible_duplicates[idx])

    original_cnt: int = len([
        name for name in os.listdir(os.path.join(project_dir, "infer-out", "error_summaries"))
        if name.endswith(".json")
    ])
    distinct_cnt: int = len(
        [name for name in os.listdir(error_summary_dir) if name.endswith(".json")])
    debug(f"Total summaries:    {original_cnt}")
    debug(f"Distinct summaries: {distinct_cnt}")


######################################################
#               Unicon preprocessing                 #
######################################################


def run_parser(project_dir: str, unitcon_path: str) -> None:
    """Wrapper function for Unitcon preprocessing procedures.

    :param project_dir: Main directory path of the target project
    :param unitcon_path: Path of the unitcon executable
    """
    debug("Running parser...")
    options: list[str] = ["-class-info", "-constant-info"]
    for option in options:
        cmd: str = " ".join([unitcon_path, project_dir, option])
        run_with_debug(cmd, cwd=os.getcwd(), shell=True, timeout=PREPROCESS_TO)


def run_command_maker(project_dir: str, unitcon_dir) -> None:
    """Wrapper function for Unitcon command maker script (`command_maker.py`).

    :param project_dir: Main directory path of the target project
    :param unitcon_dir: Path of the unitcon directory (not executable)
    """
    print_curr_time()
    debug("Running cmd maker...")
    cmd: str = " ".join([
        "python3",
        os.path.join(os.path.join(unitcon_dir, "script"), "command_maker.py"), project_dir
    ])
    run_with_debug(cmd, cwd=os.getcwd(), shell=True, timeout=PREPROCESS_TO)


######################################################
#               Unicon main program                  #
######################################################


def copy_error_summary(project_dir: str, summary_name: str) -> bool:
    """Copies the denoted error summary to unitcon_properties directory.

    :param project_dir: Main directory path of the target project
    :param summary_name: Name of the error summary file to copy
    :return: Success or failure of the copying procedure"""
    debug("Copying error summary...")
    prop_dir = os.path.join(project_dir, "unitcon_properties")

    # Remove error_summary used previously
    if os.path.isfile(os.path.join(prop_dir, "error_summaries.json")):
        debug(f"{os.path.join(prop_dir, 'error_summaries.json')} already exists. Deleting...")
        os.remove(os.path.join(prop_dir, "error_summaries.json"))

    summary_path: str = os.path.join(prop_dir, "error_summaries", summary_name)
    if os.path.isfile(summary_path):
        debug(
            f"{summary_path} exists. Copying it to {os.path.join(prop_dir, 'error_summaries.json')}..."
        )
        shutil.copyfile(
            summary_path,
            os.path.join(prop_dir, "error_summaries.json"),
        )
        return True
    debug(f"{summary_path} does not exist!")
    return False


def run_unitcon(project_dir: str, unitcon_path: str) -> None:
    """Wrapper function for main Unitcon sequence.
    Iterate over each error summary file to run Unitcon and save the results.

    :param project_dir: Main directory path of the target project
    :param unitcon_path: Path of the unitcon executable
    """
    print_curr_time()
    debug("Running unitcon...")

    error_summaries_dir = os.path.join(project_dir, "unitcon_properties", "error_summaries")
    for summary in os.listdir(error_summaries_dir):
        if summary.endswith(".json") and copy_error_summary(project_dir, summary):
            cmd: str = " ".join([unitcon_path, project_dir])
            print_curr_time()
            try:
                run_with_debug(cmd, cwd=os.getcwd(), shell=True, timeout=UNITCON_TO)
                debug("Unitcon ended!")
            except UnitconException:
                debug(f"Unitcon killed (TO: {UNITCON_TO})")

            curr_dir: str = os.path.join(project_dir, "unitcon_tests")
            results_dir: str = os.path.join(project_dir, "results_" + summary[:-5])
            if os.path.isdir(results_dir):
                debug(f"{results_dir} already exists. Deleting...")
                shutil.rmtree(results_dir)
            debug(f"Renaming {curr_dir} to {results_dir}...")
            shutil.move(curr_dir, results_dir)


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
       |- remove_duplicate_summaries()
       |  `- file_content_hash()
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
        default=os.path.abspath("unitcon-infer/infer/bin/infer"),
        help="Path of infer's executable file",
    )
    parser.add_argument(
        "--unitcon_path",
        type=pathlib.Path,
        default=os.path.abspath("unitcon"),  # Assumes `unitcon` is on PATH
        help="Path of unitcon's executable file",
    )
    parser.add_argument("-v", "--verbose", action="store_true", help="Print debug lines")
    parser.add_argument("--version",
                        type=int,
                        default=8,
                        help="Version of Java used in the project")
    args = parser.parse_args()
    abspath = os.path.abspath(args.project)
    abs_infer = os.path.abspath(args.infer_path)
    abs_unitcon = os.path.abspath(args.unitcon_path)

    global VERBOSE
    VERBOSE = args.verbose

    run_infer(abspath, str(abs_infer), args.version)
    remove_duplicate_summaries(abspath)
    run_parser(abspath, str(abs_unitcon))
    run_command_maker(abspath, str(os.path.dirname(abs_unitcon)))
    run_unitcon(abspath, str(abs_unitcon))


if __name__ == "__main__":
    main()
