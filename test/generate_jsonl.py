"""Generate a JSONL file from `algoveri_data`.

Each immediate subdirectory under `algoveri_data` is treated as a data
point. For each folder we look for `verus_nl.txt` (natural language
description) and `verus_spec.rs` (the specification). We output one JSON
object per line with the following fields:

- `task`: directory name
- `desp`: contents of `verus_nl.txt` (string)
- `spec`: contents of `verus_spec.rs` (string)

Example:
	python test/generate_jsonl.py --data algoveri_data --out test/data.jsonl
"""
from pathlib import Path
import argparse
import json
import sys


def read_text_file(p: Path) -> str:
	try:
		return p.read_text(encoding="utf-8").strip()
	except FileNotFoundError:
		return ""


def iter_tasks(data_root: Path):
	if not data_root.exists() or not data_root.is_dir():
		raise FileNotFoundError(f"data root not found: {data_root}")
	for child in sorted(data_root.iterdir()):
		if not child.is_dir():
			continue
		yield child


def generate_jsonl(data_root: Path, out_path: Path, verbose: bool = False):
	out_path.parent.mkdir(parents=True, exist_ok=True)
	with out_path.open("w", encoding="utf-8") as fout:
		for task_dir in iter_tasks(data_root):
			task_name = task_dir.name
			nl_path = task_dir / "verus_nl.txt"
			spec_path = task_dir / "verus_spec.rs"
			desp = read_text_file(nl_path)
			spec = read_text_file(spec_path)
			obj = {"task": task_name, "desc": desp, "spec": spec}
			fout.write(json.dumps(obj, ensure_ascii=False) + "\n")
			if verbose:
				print(f"Wrote {task_name}")


def main(argv=None):
	p = argparse.ArgumentParser(description="Generate JSONL from algoveri_data")
	p.add_argument("--data", default="algoveri_data", help="Root data folder (default: algoveri_data)")
	p.add_argument("--out", default="test/data.jsonl", help="Output JSONL path (default: test/data.jsonl)")
	p.add_argument("--verbose", action="store_true", help="Print progress")
	args = p.parse_args(argv)

	data_root = Path(args.data)
	out_path = Path(args.out)

	try:
		generate_jsonl(data_root, out_path, verbose=args.verbose)
	except Exception as e:
		print("Error:", e, file=sys.stderr)
		return 2
	return 0


if __name__ == "__main__":
	raise SystemExit(main())

