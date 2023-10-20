import argparse
import pathlib
import os
import shutil
import subprocess

manifest_file = "Manifest"
dependency_jar = "with_dependency.jar"
test_file_name = "UnitconTest"

def make_dependency_jar(project_dir, classpaths):
  current_dir = os.getcwd()
  os.chdir(project_dir)
  contents = 'Class-Path: ' +'\n  '.join(classpaths) + '\nMain-Class: ' + test_file_name
  with open(manifest_file, 'w') as f:
    f.write(contents)
    f.write('\n')

  command = ['jar', '-cmf', manifest_file, dependency_jar, '$(find . -name "*.jar")', '$(find . -name "classes")']
  os.system(' '.join(command)) # make dependency_jar file


def write_command(cmd_type, file):
  command = []
  if cmd_type == "build":
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
    build_file = os.path.join(file_path, "build_command")
    test_file = os.path.join(file_path, "test_command")
    write_command("build", build_file)
    write_command("test", test_file)


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("project", type=pathlib.Path, default=None,
                      help='Project directory where need to create build command files')
  args = parser.parse_args()
  make_build_command(args.project)


if __name__ == "__main__":
  main()
