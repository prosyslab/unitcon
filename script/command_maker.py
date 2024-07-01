import argparse
import pathlib
import os
import shutil
import subprocess

dependency_jar = "with_dependency.jar"


def make_dependency_jar(project_dir, classpaths):
    command = [
        'jar', '-cf', dependency_jar, '$(find . -name "*.jar")',
        '$(find . -name "*.class")'
    ]
    subprocess.run(' '.join(command), cwd=project_dir,
                   shell=True)  # make dependency_jar file


def collect_classpaths(project_dir):
    classpaths = list()
    for rootdir in [project_dir, os.path.join(project_dir, "..", "deps")]:
        if not os.path.isdir(rootdir):
            continue
        for dirpath, dirnames, filenames in os.walk(rootdir):
            for filename in filenames:
                if filename.endswith(".jar"):
                    classpaths.append(os.path.join(dirpath, filename))
            for dirname in dirnames:
                if dirname.endswith("classes"):
                    classpaths.append(os.path.join(dirpath, dirname))
    return classpaths


def make_build_command(project_dir):
    abspaths = collect_classpaths(project_dir)
    classpaths = [os.path.relpath(p, start=project_dir) for p in abspaths]
    make_dependency_jar(project_dir, classpaths)


def execute_build_cmd(project_dir):
    build_cmd_file = os.path.join(project_dir, "unitcon_properties",
                                  "build_command")
    assert os.path.isfile(build_cmd_file), f"Failed to build {project_dir}"
    with open(build_cmd_file, "r") as f:
        for cmd in f.readlines():
            subprocess.run(cmd, cwd=project_dir, shell=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "project",
        type=pathlib.Path,
        default=None,
        help='Project directory where need to create build command files')
    args = parser.parse_args()

    execute_build_cmd(args.project)
    make_build_command(args.project)


if __name__ == "__main__":
    main()
