"""Remove all empty results produced by Unitcon"""

import argparse
import os


def remove_empty_tcs(result_dir: str) -> None:
    """Removes empty testcases, both due to timeout or queue exhaustion.

    :param result_dir: Path to the result directory created by Unitcon
    """
    if not os.path.isdir(result_dir):
        raise FileNotFoundError(f"Directory not found: {result_dir}")

    total_cnt: int = 0
    empty_cnt: int = 0

    for filename in os.listdir(result_dir):
        if not (
            len(filename) > 7 and filename[:7] == "result-" and filename[7:].isdigit()
        ):
            continue
        remove: bool = False
        total_cnt += 1
        with open(os.path.join(result_dir, filename), "r", encoding="utf-8") as f:
            lines: list[str] = f.readlines()

            if len(lines) < 2 or lines[1].strip() == "time-out":
                remove = True
                empty_cnt += 1
                print(f"Removing {filename}")

        if remove:
            os.remove(os.path.join(result_dir, filename))

    print("\n=================================================\n")
    print(f"Total files: {total_cnt}")
    print(f"Empty files: {empty_cnt}")
    print(f"Remaining:   {total_cnt - empty_cnt}")


def main() -> None:
    """Removes empty testcases found in the provided result directory."""
    parser: argparse.ArgumentParser = argparse.ArgumentParser()
    parser.add_argument(
        "result_dir",
        type=str,
        default=None,
        help="Path to the result directory created by Unitcon",
    )
    args: argparse.Namespace = parser.parse_args()
    remove_empty_tcs(args.result_dir)


if __name__ == "__main__":
    main()
