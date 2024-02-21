"""Remove all empty results produced by Unitcon"""

import argparse
import os
import shutil


def remove_empty_dirs(project_dir: str) -> None:
    """Removes empty testcases, both due to timeout or queue exhaustion.

    :param project_dir: Main directory path of the target project
    """
    all_result_dirs: list[str] = [
        result_dir
        for result_dir in os.listdir(project_dir)
        if os.path.isdir(os.path.join(project_dir, result_dir))
        and result_dir.startswith("results_")
    ]
    exclude_files: set[str] = {
        "log.txt",
        "UnitconEnum.java",
        "UnitconEnum.class",
        "UnitconInterface.java",
        "UnitconInterface.class",
    }

    empty_cnt: int = 0
    tc_cnt: int = 0
    for result_dir in all_result_dirs:
        is_empty: bool = True
        full_path: str = os.path.join(project_dir, result_dir)
        all_files = os.listdir(full_path)

        for file in all_files:
            if not file in exclude_files:
                is_empty = False
                break

        if is_empty:
            empty_cnt += 1
            print(f"Empty results: {result_dir}")
            shutil.rmtree(full_path)
        else:
            tc_cnt += len(set(all_files) - exclude_files) // 2

    print("\n=================================================\n")
    print(f"Total dirs: {len(all_result_dirs)}")
    print(f"Empty dirs: {empty_cnt}")
    print(f"Remaining : {len(all_result_dirs) - empty_cnt}")
    print(f"Testcases : {tc_cnt}")


def main() -> None:
    """Removes empty testcases found in the provided result directory."""
    parser: argparse.ArgumentParser = argparse.ArgumentParser()
    parser.add_argument(
        "project_dir",
        type=str,
        default=None,
        help="Path to the project directory analyzed by Unitcon",
    )
    args: argparse.Namespace = parser.parse_args()
    remove_empty_dirs(args.project_dir)


if __name__ == "__main__":
    main()
