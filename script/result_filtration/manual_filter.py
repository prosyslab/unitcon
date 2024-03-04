"""Filters test cases in case of abnormal termination of UnitCon"""

import os
import subprocess
import shutil
import argparse
import pathlib
import re
import json
from concurrent.futures import ThreadPoolExecutor


def compile_and_delete(result_path: str, project_path: str) -> None:
    """Compiles all java files in the given path and removes those that can't be compiled."""
    print("Attempting compilation...")
    while True:
        os.system(f'find {result_path} -name "*.java" > java_files')
        result: subprocess.CompletedProcess[bytes] = subprocess.run(
            " ".join(
                [
                    "javac",
                    "-cp",
                    os.path.join(project_path, "with_dependency.jar"),
                    "@java_files",
                    "-Xmaxerrs",
                    "200",
                ]
            ),
            check=False,
            shell=True,
            capture_output=True,
        )
        print(result.stdout.decode())
        print(result.stderr.decode())
        if result.returncode == 0 or check_empty(result_path):
            break
        assert result.stderr is not None
        error_msg: list[str] = result.stderr.decode("utf-8").split("\n")
        for line in error_msg:
            if re.search(".*UnitconTest[0-9]+\\.java.*", line):
                file_name: str = line.split(":")[0]
                if os.path.isfile(file_name):
                    print(f"Removing file: {file_name}")
                    os.remove(file_name)


def check_empty(result_path: str) -> bool:
    """Checks if the given result directory is empty, i.e., contains no viable test cases."""
    files: list[str] = [
        f
        for f in os.listdir(result_path)
        if os.path.isfile(os.path.join(result_path, f))
        and f != "log.txt"
        and not (f.startswith("UnitconEnum.") or f.startswith("UnitconInterface."))
    ]
    return len(files) == 0


def targetted_method(project_path: str, result_cnt: int) -> str:
    """Returns the name of the target method."""
    summary_file: str = os.path.join(
        project_path, "unitcon_properties", "error_summarys", f"{result_cnt}.json"
    )
    with open(summary_file, "r", encoding="utf-8") as f:
        return json.load(f)["Procname"].strip().split("(")[0]


def check_targetted_method(output: str, target: str) -> bool:
    """Checks whether the provided output indicates an exception caused by the target method."""
    return target in output.strip().split("\n")[-2]


def check_npe(output: str, package: str) -> bool:
    """Checks whether the provided output indicates a nontrivial NPE."""
    return (
        "java.lang.NullPointerException" in output
        and package in output
        and not (
            "java.io.File.<init>" in output
            or "java.io.FileInputStream.<init>" in output
            or "java.io.FileOutputStream.<init>" in output
            or "java.util.Objects.requireNonNull" in output
        )
        and len(output.strip().split("\n")) > 3
    )


def remove_useless_files(
    result_path: str, project_path: str, project_name: str, result_cnt: int
) -> None:
    """Removes test cases that do not throw the desired NPE."""
    print("Removing useless test cases...")
    class_files: list[str] = [
        f
        for f in os.listdir(result_path)
        if f.endswith(".class")
        and f != "UnitconEnum.class"
        and f != "UnitconInterface.class"
    ]
    print(f"There are {len(class_files)} files to test...")
    target_method: str = targetted_method(project_path, result_cnt)
    print(f"{target_method=}")

    def process_class_file(f):
        java_file: str = f[:-6]
        result = subprocess.run(
            [
                "java",
                "-cp",
                os.path.join(project_path, "with_dependency.jar") + ":" + result_path,
                java_file,
            ],
            capture_output=True,
            check=False,
        )
        if result.returncode == 0:
            print(f"Removing files: {java_file}.java, {f}")
            os.remove(os.path.join(result_path, java_file + ".java"))
            os.remove(os.path.join(result_path, f))
            return

        output: str = result.stderr.decode("utf-8")
        if not check_targetted_method(output, target_method) or not check_npe(
            output, project_name
        ):
            print(f"Removing files: {java_file}.java, {f}")
            os.remove(os.path.join(result_path, java_file + ".java"))
            os.remove(os.path.join(result_path, f))

    with ThreadPoolExecutor() as executor:
        executor.map(process_class_file, class_files)


def main() -> None:
    """Checks each test case in the given result directory, and removes irrelevant ones."""
    parser: argparse.ArgumentParser = argparse.ArgumentParser()
    parser.add_argument(
        "project_path",
        type=pathlib.Path,
        help="Path to the result directory",
    )
    parser.add_argument(
        "result_cnt", type=int, help="The number of the result directory to filter"
    )

    args: argparse.Namespace = parser.parse_args()
    project_path: str = str(os.path.abspath(args.project_path))
    result_cnt: int = args.result_cnt
    result_path: str = os.path.join(project_path, f"results_{result_cnt}")

    with open(
        os.path.join(project_path, "unitcon_properties", "expected_bug"),
        "r",
        encoding="utf-8",
    ) as f:
        project_name: str = f.readline().strip()

    print(f"{result_path=}")
    print(f"{project_path=}")
    print(f"{project_name=}")

    compile_and_delete(result_path, project_path)
    remove_useless_files(result_path, project_path, project_name, result_cnt)

    print("Checking if the directory is empty...")
    if check_empty(result_path):
        print(f"Removing directory {result_path}")
        shutil.rmtree(result_path)


if __name__ == "__main__":
    main()
