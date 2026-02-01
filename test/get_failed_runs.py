"""Scan completed verus run logs and report which tasks failed for a model.

Usage:
    python test/get_failed_runs.py --logs test_results/verus --model Qwen3-... 

This script lists tasks present under `data_root` that do not have a
corresponding successful log file for the given model. By default it will
attempt to read each matched log JSON and consider it successful only if the
top-level `verified` field is True; use `--no-check` to treat any existing
log file as success.
"""
from pathlib import Path
import json
import argparse
from typing import List


def find_tasks(data_root: Path) -> List[str]:
    """Return a list of immediate subdirectory names under data_root.

    We treat each child directory as one task name.
    """
    if not data_root.exists() or not data_root.is_dir():
        raise FileNotFoundError(f"data root not found: {data_root}")
    tasks = [p.name for p in sorted(data_root.iterdir()) if p.is_dir()]
    return tasks


def scan_logs_for_model(logs_dir: Path, model_name: str, suffix: str = "_verus.json", check_verified: bool = False) -> List[str]:
    """Return a list of task names that have successful logs for model_name.

    Filenames are expected to be of the form: <model>_<task>{suffix}
    The function extracts the <task> portion by removing the leading
    "{model_name}_" and the trailing `suffix`.
    If `check_verified` is True, the JSON file will be parsed and considered
    successful only if the top-level `verified` key is True.
    """
    if not logs_dir.exists() or not logs_dir.is_dir():
        raise FileNotFoundError(f"logs dir not found: {logs_dir}")

    successful = []
    prefix = model_name + "_"
    for p in logs_dir.iterdir():
        if not p.is_file():
            continue
        name = p.name
        if not name.startswith(prefix):
            continue
        # remove prefix
        rest = name[len(prefix):]
        if rest.endswith(suffix):
            task = rest[: -len(suffix)]
        else:
            # strip .json if present, otherwise take rest as task
            if rest.endswith('.json'):
                task = rest[: -5]
            else:
                task = rest

        if check_verified:
            try:
                data = json.loads(p.read_text())
                # look for top-level 'verified' boolean or nested details
                ok = data.get("verified") if isinstance(data, dict) else False
                if ok:
                    successful.append(task)
            except Exception:
                # if parsing fails, skip this log
                continue
        else:
            successful.append(task)

    return sorted(successful)


def find_failed_tasks(data_root: Path, logs_dir: Path, model_name: str, suffix: str = "_verus.json", check_verified: bool = False) -> List[str]:
    tasks = find_tasks(data_root)
    succeeded = scan_logs_for_model(logs_dir, model_name, suffix=suffix, check_verified=check_verified)
    failed = [t for t in tasks if t not in succeeded]
    return failed


def main(argv=None):
    p = argparse.ArgumentParser(description="Find failed tasks for a given model by scanning verus logs.")
    p.add_argument("--logs", required=True, help="Directory containing per-task JSON logs (e.g., test_results/verus)")
    p.add_argument("--model", required=True, help="Model name prefix used in log filenames")
    p.add_argument("--data", default="algoveri_data", help="Root folder containing tasks (default: algoveri_data)")
    p.add_argument("--suffix", default="_verus.json", help="Suffix used in log filenames (default: _verus.json)")
    p.add_argument("--no-check", dest="check", action="store_false", help="Do not parse JSON; treat any existing log file as success")
    args = p.parse_args(argv)

    data_root = Path(args.data)
    logs_dir = Path(args.logs)

    failed = find_failed_tasks(data_root, logs_dir, args.model, suffix=args.suffix, check_verified=args.check)

    if not failed:
        print("No failed tasks found — all tasks have successful logs for model:", args.model)
        return 0

    print("Failed tasks for model", args.model)
    for t in failed:
        print(t)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
