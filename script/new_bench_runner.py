import argparse
import pathlib
import os
import shutil
import subprocess


VERBOSE = False


def debug(msg):
    if VERBOSE:
        print("[DEBUG]" + msg)


def run_with_debug(cmd, *args, **kwargs):
    debug(f"Running command: {cmd.strip()}")
    debug(f"{args=}")
    debug(f"{kwargs=}")
    output = subprocess.run(cmd, *args, **kwargs, capture_output=True)
    debug(f"Output:\n{output.stdout.decode('utf-8')}")


def execute_build_cmd(project_dir, infer_path):
    debug(f"Executing build cmd: {project_dir=} {infer_path=}")
    build_cmd_file = os.path.join(
        project_dir, "unitcon_properties", "unitcon_build_command"
    )
    assert os.path.isfile(build_cmd_file), f"Failed to build {project_dir}"
    with open(build_cmd_file, "r") as f:
        for cmd in f.readlines():
            if cmd.startswith("mvn dependency"):
                continue
            if cmd.startswith("mvn clean"):
                cmd = " ".join([infer_path, "capture", "--", cmd])
                run_with_debug(cmd, cwd=project_dir, shell=True)
            else:
                run_with_debug(cmd, cwd=project_dir, shell=True)


def execute_analyzer(project_dir, infer_path):
    debug("Executing analyzer...")
    cmd = " ".join([infer_path, "analyze", "--pulse-only", "--show-latent"])
    run_with_debug(cmd, cwd=project_dir, shell=True)


def execute_summary_maker(project_dir, infer_path):
    debug("Executing summary maker...")
    summary_file = os.path.join(project_dir, "infer-out", "summary.json")
    cmd = " ".join([infer_path, "debug", "--procedures", "--procedures-summary-json"])

    debug(f"Running command: {cmd}")
    debug("args=()")
    debug("kwargs={{'cwd': 'project_dir', 'shell': True}}")
    result = subprocess.run(cmd, cwd=project_dir, shell=True, capture_output=True)
    with open(summary_file, "wb") as f:
        debug(f"Writing result to {summary_file}...")
        f.write(result.stdout)


def mk_error_summary_file(dirpath, error_count, buf):
    debug("Making error summary file...")

    file_path = os.path.join(dirpath, str(error_count) + ".json")
    debug(f"{file_path=}")
    with open(file_path, "w") as f:
        f.write(buf)


def split_error_summary(dirpath, summary):
    debug(f"Splitting error summary: {dirpath=} {summary=}")
    src_lines = []
    buf = ""
    error_count = 0
    with open(summary, "r") as f:
        src_lines = f.readlines()
        debug(f"{src_lines=}")
    for i in src_lines:
        debug(f"Current line: {i}")
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


def split_error_summaries(project_dir):
    debug("Splitting error summary...")
    err_summary = os.path.join(project_dir, "error_summaries.json")
    summaries_dir = os.path.join(project_dir, "error_summaries")
    if os.path.isdir(summaries_dir):
        debug(f"{summaries_dir} already exists. Removing...")
        shutil.rmtree(summaries_dir)
    debug(f"Making directory: {summaries_dir}")
    os.mkdir(summaries_dir)
    split_error_summary(summaries_dir, err_summary)


def copy_summary(project_dir):
    debug("Copying summary...")
    org_path = os.path.join(project_dir, "infer-out")
    new_path = os.path.join(project_dir, "unitcon_properties")
    if os.path.isfile(os.path.join(org_path, "summary.json")):
        debug(f"Copying file {org_path} to {new_path}")
        if os.path.isdir(os.path.join(new_path, "error_summaries")):
            debug(
                f"{os.path.join(new_path, 'error_summaries')} already exists. Removing..."
            )
            shutil.rmtree(os.path.join(new_path, "error_summaries"))
        split_error_summaries(org_path)

        debug(f"Copying relevant summaries from {org_path} to {new_path}...")
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


def run_infer(project_dir, infer_path):
    debug("Running infer...")
    execute_build_cmd(project_dir, infer_path)
    execute_analyzer(project_dir, infer_path)
    execute_summary_maker(project_dir, infer_path)
    copy_summary(project_dir)


def run_parser(project_dir, encoding):
    debug("Running parser...")
    script_list = [
        "constant_collector.py",
        "enum_parser.py",
        "inheritance_info_parser.py",
    ]
    for script in script_list:
        cmd = " ".join(
            [
                "source",
                "venv/bin/activate;" "python3",
                os.path.join("script", script),
                project_dir,
                "--encoding",
                encoding,
            ]
        )
        debug(f"Running command: {cmd}")
        os.system("bash -c " + '"' + cmd + '"')


def run_command_maker(project_dir, build_type):
    debug("Running cmd maker...")
    cmd = " ".join(
        ["python3", os.path.join("script", "command_maker.py"), project_dir, build_type]
    )
    run_with_debug(cmd, cwd=os.getcwd(), shell=True)


def copy_error_summary(project_dir, error_count):
    debug("Copying error summary...")
    prop_dir = os.path.join(project_dir, "unitcon_properties")

    # Remove error_summary used previously
    if os.path.isfile(os.path.join(prop_dir, "error_summaries.json")):
        debug(
            f"{os.path.join(prop_dir, 'error_summaries.json')} already exists. Deleting..."
        )
        os.remove(os.path.join(prop_dir, "error_summaries.json"))

    if os.path.isfile(os.path.join(prop_dir, "error_summaries", str(error_count))):
        debug(
            f"{os.path.join(prop_dir, 'error_summaries', str(error_count))} exists. Copying it to {os.path.join(prop_dir, 'error_summaries.json')}..."
        )
        shutil.copyfile(
            os.path.join(prop_dir, "error_summaries", str(error_count)),
            os.path.join(prop_dir, "error_summaries.json"),
        )
        return True
    debug(
        f"{os.path.join(prop_dir, 'error_summaries', str(error_count))} does not exist!"
    )
    return False


def run_unitcon(project_dir):
    debug("Running unitcon...")
    error_count = 0
    result_dir = os.path.join(os.getcwd(), os.path.basename(project_dir) + "-result")

    if os.path.isdir(result_dir):
        debug(f"{result_dir} already exists. Deleting...")
        shutil.rmtree(result_dir)
    debug(f"Creating directory {result_dir}...")
    os.mkdir(result_dir)

    while copy_error_summary(project_dir, error_count):
        result_file = os.path.join(result_dir, "-" + str(error_count))
        cmd = " ".join(["unitcon", project_dir])

        debug(f"Running command: {cmd}")
        debug("args=()")
        debug(
            f"kwargs={{'cwd': {os.getcwd()}, 'shell': True, 'stdout': {subprocess.PIPE}, 'universal_newlines': True}}"
        )
        process = subprocess.Popen(
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
            f.write(out)
        error_count += 1


def main():
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
        "--encoding", type=str, default="utf-8", help="Encoding type of project"
    )
    parser.add_argument(
        "--build_type", type=str, default="maven", help="[maven | javac]"
    )
    parser.add_argument("--verbose", type=bool, default=False, help="Print debug lines")
    args = parser.parse_args()
    abspath = os.path.abspath(args.project)

    global VERBOSE
    VERBOSE = args.verbose

    run_infer(abspath, str(args.infer_path))
    run_parser(abspath, args.encoding)
    run_command_maker(abspath, args.build_type)
    run_unitcon(abspath)


if __name__ == "__main__":
    main()
