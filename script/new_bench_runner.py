import argparse
import pathlib
import os
import shutil
import subprocess


def execute_build_cmd(project_dir, infer_path):
    build_cmd_file = os.path.join(project_dir, "unitcon_properties",
                                  "unitcon_build_command")
    assert os.path.isfile(build_cmd_file), f"Failed to build {project_dir}"
    with open(build_cmd_file, "r") as f:
        for cmd in f.readlines():
            if cmd.startswith("mvn dependency"):
                continue
            elif cmd.startswith("mvn clean"):
                cmd = ' '.join([infer_path, "capture", "--", cmd])
                subprocess.run(cmd, cwd=project_dir, shell=True)
            else:
                subprocess.run(cmd, cwd=project_dir, shell=True)


def execute_analyzer(project_dir, infer_path):
    cmd = ' '.join([infer_path, "analyze", "--pulse-only", "--show-latent"])
    subprocess.run(cmd, cwd=project_dir, shell=True)


def execute_summary_maker(project_dir, infer_path):
    summary_file = os.path.join(project_dir, "infer-out", "summary.json")
    cmd = ' '.join(
        [infer_path, "debug", "--procedures", "--procedures-summary-json"])
    result = subprocess.run(cmd,
                            cwd=project_dir,
                            shell=True,
                            capture_output=True)
    with open(summary_file, "wb") as f:
        f.write(result.stdout)


def mk_error_summary_file(dirpath, error_count, buf):
    with open(os.path.join(dirpath, str(error_count) + '.json'), 'w') as f:
        f.write(buf)


def split_error_summary(dirpath, summary):
    src_lines = []
    buf = ""
    error_count = 0
    with open(summary, 'r') as f:
        src_lines = f.readlines()
    for i in src_lines:
        if "\"Procname\"" in i and "\"BoItv\"" in i:
            buf = i
            mk_error_summary_file(dirpath, error_count, buf)
            error_count += 1
            buf = ""
        elif "\"BoItv\"" in i:
            buf += i
            mk_error_summary_file(dirpath, error_count, buf)
            error_count += 1
            buf = ""
        else:
            buf += i


def split_error_summarys(project_dir):
    err_summary = os.path.join(project_dir, 'error_summarys.json')
    summarys_dir = os.path.join(project_dir, 'error_summarys')
    os.mkdir(summarys_dir)
    split_error_summary(summarys_dir, err_summary)


def copy_summary(project_dir):
    org_path = os.path.join(project_dir, 'infer-out')
    new_path = os.path.join(project_dir, 'unitcon_properties')
    if os.path.isfile(os.path.join(org_path, "summary.json")):
        if os.path.isdir(os.path.join(new_path, "error_summarys")):
            shutil.rmtree(os.path.join(new_path, "error_summarys"))
        split_error_summarys(org_path)
        shutil.copytree(os.path.join(org_path, "error_summarys"),
                        os.path.join(new_path, "error_summarys"))
        shutil.copyfile(os.path.join(org_path, "summary.json"),
                        os.path.join(new_path, "summary.json"))
        shutil.copyfile(os.path.join(org_path, "call_proposition.json"),
                        os.path.join(new_path, "call_proposition.json"))
    else:
        print(f"Failed to build {project_dir}")


def run_infer(project_dir, infer_path):
    execute_build_cmd(project_dir, infer_path)
    execute_analyzer(project_dir, infer_path)
    execute_summary_maker(project_dir, infer_path)
    copy_summary(project_dir)


def run_parser(project_dir, encoding):
    venv = ' '.join(['source', 'venv/bin/active'])
    subprocess.run(venv, cwd=os.getcwd(), shell=True, capture_output=True)
    script_list = [
        'constant_collector.py', 'enum_parser.py', 'inheritance_info_parser.py'
    ]
    for script in script_list:
        cmd = ' '.join([
            'python3',
            os.path.join('script', script), project_dir, "--encoding", encoding
        ])
        subprocess.run(cmd, cwd=os.getcwd(), shell=True, capture_output=True)
    # The end of executing parsers
    subprocess.run('deactivate',
                   cwd=os.getcwd(),
                   shell=True,
                   capture_output=True)


def run_command_maker(project_dir, build_type):
    cmd = ' '.join([
        'python3',
        os.path.join('script', 'command_maker.py'), project_dir, build_type
    ])
    subprocess.run(cmd, cwd=os.getcwd(), shell=True, capture_output=True)


def copy_error_summary(project_dir, error_count):
    prop_dir = os.path.join(project_dir, 'unitcon_properties')
    # Remove error_summary used in previous
    if os.path.isfile(os.path.join(prop_dir, 'error_summarys.json')):
        os.remove(os.path.join(prop_dir, 'error_summarys.json'))
    if os.path.isfile(
            os.path.join(prop_dir, 'error_summarys', str(error_count))):
        shutil.copyfile(
            os.path.join(prop_dir, 'error_summarys', str(error_count)),
            os.path.join(prop_dir, 'error_summarys.json'))
        return True
    else:
        return False


def run_unitcon(project_dir):
    error_count = 0
    result_dir = os.path.join(os.getcwd(),
                              os.path.basename(project_dir) + '-result')
    os.mkdir(result_dir)
    while (copy_error_summary(project_dir, error_count)):
        result_file = os.path.join(result_dir, '-' + str(error_count))
        cmd = ' '.join(['unitcon', project_dir])
        process = subprocess.Popen(cmd,
                                   cwd=os.getcwd(),
                                   shell=True,
                                   stdout=subprocess.PIPE,
                                   universal_newlines=True)
        # Wait for ending of UnitCon
        process.wait()
        out, _ = process.communicate()
        with open(result_file, "wb") as f:
            f.write(out)
        error_count += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("project",
                        type=pathlib.Path,
                        default=None,
                        help='Project directory where need to execute UnitCon')
    parser.add_argument("--infer_path",
                        type=pathlib.Path,
                        default="/infer/infer/bin/infer",
                        help="Path of infer's executable file")
    parser.add_argument("--encoding",
                        type=str,
                        default="utf-8",
                        help='Encoding type of project')
    parser.add_argument("--build_type",
                        type=str,
                        default="maven",
                        help='[maven | javac]')
    args = parser.parse_args()
    abspath = os.path.abspath(args.project)
    run_infer(abspath, str(args.infer_path))
    run_parser(abspath, args.encoding)
    run_command_maker(abspath, args.build_type)
    run_unitcon(abspath)


if __name__ == "__main__":
    main()
