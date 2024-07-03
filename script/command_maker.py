import argparse
import pathlib
import os
import shutil
import subprocess

MANIFEST_FILE = "Manifest"
DEPENDENCY_JAR = "with_dependency.jar"


def collect_classpaths(project_dir):
    classpaths = list()
    for rootdir in [project_dir, os.path.join(project_dir, "..", "deps")]:
        if not os.path.isdir(rootdir):
            continue
        for dirpath, dirnames, filenames in os.walk(rootdir):
            for filename in filenames:
                if filename.endswith(".jar"):
                    classpaths.append(os.path.join(dirpath, filename))
                elif filename.endswith(".class"):
                    classpaths.append(os.path.join(dirpath, filename))
    return classpaths


def make_jar_with_dependencies(project_dir):
    abspaths = collect_classpaths(project_dir)
    classpaths = [os.path.relpath(p, start=project_dir) for p in abspaths]

    with open(os.path.join(project_dir, MANIFEST_FILE), 'w') as f:
        f.write('Class-Path: ' + '\n  '.join(classpaths))
        f.write("\n")

    with open(os.path.join(project_dir, "jar_files"), "w") as f:
        f.write("\n".join(classpaths))
        f.write("\n")

    command = "jar -cmf Manifest with_dependency.jar @jar_files"
    try:
        output = subprocess.check_output(command,
                                         cwd=project_dir,
                                         stderr=subprocess.STDOUT,
                                         shell=True)
    except subprocess.CalledProcessError as ex:
        output = ex.output
    return output.decode()


def execute_build_cmd(project_dir):
    build_cmd_file = os.path.join(project_dir, "unitcon_properties", "build_command")
    assert os.path.isfile(build_cmd_file), f"Failed to find build command file {build_cmd_file}"

    with open(build_cmd_file, "r") as f:
        commands = f.readlines()

    outputs = []
    try:
        for cmd in commands:
            output = subprocess.check_output(cmd,
                                             cwd=project_dir,
                                             stderr=subprocess.STDOUT,
                                             shell=True)
            outputs.append(output.decode())
    except subprocess.CalledProcessError as ex:
        outputs.append(ex.output.decode())
    return "\n".join(outputs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("project",
                        type=pathlib.Path,
                        default=None,
                        help='Project directory where need to create build command files')
    args = parser.parse_args()

    execute_build_cmd(args.project)
    make_jar_with_dependencies(args.project)


if __name__ == "__main__":
    main()
