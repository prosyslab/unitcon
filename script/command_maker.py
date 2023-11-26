import argparse
import pathlib
import os
import shutil
import subprocess

manifest_file_name = "Manifest"
dependency_jar = "with_dependency.jar"
test_file_name = "UnitconTest"

def make_java_files(project_dir):
    java_files = os.path.join(project_dir, "java_files")
    unitcon_files = os.path.join(project_dir, "unitcon_files")
    if os.path.isfile(java_files):
        lines = []
        with open (java_files, 'r') as f:
            lines = f.readlines()
        with open(unitcon_files, 'w') as f:
            for line in lines:
                if "Main.java" in line:
                    f.write(line.replace("Main.java", "UnitconTest.java"))
                else:
                    f.write(line)

def copy_build_cmd(project_dir):
    file_path = os.path.join(project_dir, "unitcon_properties")
    lines = []
    with open (os.path.join(file_path, "build_command"), 'r') as f:
        lines = f.readlines()
    with open(os.path.join(file_path, "compile_command"), 'w') as f:
        for line in lines:
            if "@java_files" in line:
                f.write(line.replace("@java_files", "@unitcon_files"))
            else:
                f.write(line)

def modify_test_cmd(project_dir):
    file_path = os.path.join(project_dir, "unitcon_properties")
    lines = []
    with open (os.path.join(file_path, "test_command"), 'r') as f:
        lines = f.readlines()
    with open(os.path.join(file_path, "test_command"), 'w') as f:
        for line in lines:
            if "Main" in line:
                f.write(line.replace("Main", "UnitconTest"))
            else:
                f.write(line)


def make_dependency_jar(project_dir, classpaths):
    manifest_file = os.path.join(project_dir, manifest_file_name)
    contents = 'Class-Path: ' + '\n  '.join(
        classpaths) + '\nMain-Class: ' + test_file_name
    with open(manifest_file, 'w') as f:
        f.write(contents)
        f.write('\n')

    command = [
        'jar', '-cmf', manifest_file_name, dependency_jar,
        '$(find . -name "*.jar")', '$(find . -name "classes")'
    ]
    subprocess.run(' '.join(command), cwd=project_dir,
                   shell=True)  # make dependency_jar file


def write_command(cmd_type, file):
    command = []
    if cmd_type == "compile":
        command = ["javac", "-cp", dependency_jar, test_file_name + ".java"]
    elif cmd_type == "test":
        command = ["java", "-cp", dependency_jar + ":.", test_file_name]
    assert len(command) > 0, "Failed to make command line"

    with open(file, 'w') as f:
        f.write(' '.join(command))
        f.write('\n')


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

    file_path = os.path.join(project_dir, "unitcon_properties")
    build_file = os.path.join(file_path, "compile_command")
    test_file = os.path.join(file_path, "test_command")
    write_command("compile", build_file)
    write_command("test", test_file)


def execute_build_cmd(project_dir):
    build_cmd_file = os.path.join(project_dir, "unitcon_properties",
                                  "unitcon_build_command")
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
    parser.add_argument(
        "build_type",
        type=str,
        default=None,
        help='maven or javac')
    args = parser.parse_args()
    
    if args.build_type == "maven":
        execute_build_cmd(args.project)
        make_build_command(args.project)
    elif args.build_type == "javac":
        path = os.path.join(args.project)
        make_java_files(path)
        copy_build_cmd(path)
        modify_test_cmd(path)


if __name__ == "__main__":
    main()
