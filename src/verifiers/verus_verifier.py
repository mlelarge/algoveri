"""Verus (Rust + verus) verifier adapter.

This verifier writes the provided `source` string to a temporary `.rs` file
under the configured results directory and invokes the `verus` executable.

Configuration lookup order for `VERUS_PATH` and `RESULTS_DIR`:
  1. explicit kwargs passed to the constructor
  2. environment variables `VERUS_PATH` and `RESULTS_DIR`
  3. `config/config.yaml` file in repo root (simple key: value parser)
  4. sensible defaults
"""
from .base import BaseVerifier
from typing import Dict, Any, Optional
from pathlib import Path
import subprocess
import tempfile
import os
import time


def _read_simple_config(path: Path) -> Dict[str, str]:
    """Read a simple YAML config file and return flat string dict.

    Behavior:
      - If `PyYAML` is available, parse with `yaml.safe_load` and return
        a stringified mapping of top-level keys.
      - If PyYAML is not available or parsing fails, fall back to a
        simple `key: value` line parser (the previous implementation).

    The function intentionally keeps the return type simple (str->str)
    because callers expect string-like values for paths.
    """
    cfg: Dict[str, str] = {}
    if not path.exists():
        return cfg

    raw = path.read_text()
    if not raw.strip():
        return cfg

    # Prefer PyYAML if available (handles full YAML syntax)
    try:
        import yaml  # type: ignore

        parsed = yaml.safe_load(raw)
        if isinstance(parsed, dict):
            for k, v in parsed.items():
                # convert values to simple strings to keep callers simple
                cfg[str(k)] = "" if v is None else str(v)
            return cfg
    except Exception:
        # fall through to the simple parser on any error
        pass

    # Fallback simple parser (legacy behavior)
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if ":" in line:
            k, v = line.split(":", 1)
            cfg[k.strip()] = v.strip()
    return cfg


class VerusVerifier(BaseVerifier):
    def __init__(self, verus_path: Optional[str] = None, results_dir: Optional[str] = None, config_path: Optional[str] = None, timeout: int = 60):
        # Resolve config from kwargs, env, config file, defaults
        self.timeout = int(timeout)
        config_file = Path(config_path) if config_path else Path(__file__).resolve().parents[2] / "config" / "config.yaml"
        file_cfg = _read_simple_config(config_file)

        self.verus_path = (
            verus_path
            or os.environ.get("VERUS_PATH")
            or file_cfg.get("VERUS_PATH")
            or "/usr/local/bin"
        )

        self.results_dir = (
            results_dir
            or os.environ.get("RESULTS_DIR")
            or file_cfg.get("RESULTS_DIR")
            or "results/verus"
        )

        # Ensure results dir exists
        Path(self.results_dir).mkdir(parents=True, exist_ok=True)

    def _verus_executable(self) -> Path:
        # verus binary expected at VERUS_PATH/verus or just verus_path if file
        p = Path(self.verus_path)
        if p.is_file() and os.access(p, os.X_OK):
            return p
        candidate = p / "verus"
        if candidate.exists() and os.access(candidate, os.X_OK):
            return candidate
        # fallback to system PATH lookup
        from shutil import which

        sys_cand = which("verus")
        if sys_cand:
            return Path(sys_cand)
        raise FileNotFoundError(f"verus executable not found at {self.verus_path} or in PATH")

    def verify(self, source: str, spec: str, filename: Optional[str] = None, **kwargs: Any) -> Dict[str, Any]:
        """Write `source` to an .rs file and run the verus verifier on it.

        Returns a dict with keys:
          - `ok`: bool
          - `reason`: str (optional)
          - `raw`: raw subprocess output
          - `file`: path to the written .rs file
        """
        # Determine file name
        ts = int(time.time() * 1000)
        safe_name = (filename or "submission").replace("/", "_")
        out_name = f"{safe_name}_{ts}.rs"
        out_path = Path(self.results_dir) / out_name

        out_path.write_text(source)

        try:
            verus_exec = self._verus_executable()
        except FileNotFoundError as e:
            return {"ok": False, "reason": str(e), "raw": None, "file": str(out_path)}

        cmd = [str(verus_exec), str(out_path)]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=self.timeout)
            stdout = proc.stdout
            stderr = proc.stderr
            rc = proc.returncode
            raw = {"stdout": stdout, "stderr": stderr, "returncode": rc}
            ok = (rc == 0)
            reason = None if ok else f"verus exited with code {rc}"
            return {"ok": ok, "reason": reason, "raw": raw, "file": str(out_path)}
        except subprocess.TimeoutExpired as e:
            return {"ok": False, "reason": f"timeout after {self.timeout}s", "raw": None, "file": str(out_path)}
        except Exception as e:
            return {"ok": False, "reason": str(e), "raw": None, "file": str(out_path)}


