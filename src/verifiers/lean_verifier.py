"""Lean (4) verifier adapter using Apptainer.

This verifier assumes the existence of a pre-built Lean project (with lakefile.lean)
and verifies code by injecting it into that project context.
"""
from .base import BaseVerifier
from typing import Dict, Any, Optional, List
from pathlib import Path
import subprocess
import time
import os
import yaml

class LeanVerifier(BaseVerifier):
    def __init__(self, config_path: Optional[str] = None):
        self.config = self._load_config(config_path)
        
        self.lean_cfg = self.config.get("lean", {})
        self.timeout = self.lean_cfg.get("timeout", 300)
        self.method = self.lean_cfg.get("method", "apptainer")
        
        # We don't strictly use a global 'results_dir' for the .lean file itself
        # because the file needs to live inside the project to pick up dependencies.
        # However, we can use it for logging if needed.

    def _load_config(self, path: Optional[str]) -> Dict[str, Any]:
        if path:
            p = Path(path)
        else:
            p = Path(__file__).resolve().parents[2] / "config" / "config.yaml"
        
        if not p.exists():
            return {}
        try:
            with open(p, 'r') as f:
                return yaml.safe_load(f) or {}
        except Exception as e:
            print(f"Config load error: {e}")
            return {}

    def _build_command(self, source_file_path: Path) -> List[str]:
        """Construct the Apptainer command for Lean."""
        
        if self.method == "apptainer":
            cfg = self.lean_cfg.get("apptainer", {})
            image = cfg.get("image_path")
            host_elan = cfg.get("elan_home")
            host_project = cfg.get("project_path")
            
            if not image or not Path(image).exists():
                raise FileNotFoundError(f"Lean image not found: {image}")
            if not host_elan or not Path(host_elan).exists():
                raise FileNotFoundError(f"Elan home not found: {host_elan}")
            if not host_project or not Path(host_project).exists():
                raise FileNotFoundError(f"Lean project not found: {host_project}")

            # Define internal mount points
            container_elan = "/elan_home"
            container_work = "/work"

            # Based on your provided command:
            # --env ELAN_HOME=/elan_home/.elan_data
            # --env PATH=/elan_home/lean_bin/bin:$PATH
            # Note: The exact internal path for 'bin' depends on your folder structure. 
            # I am following your snippet: `/elan_home/lean_bin/bin`
            
            cmd = [
                "apptainer", "exec",
                # Bind Elan toolchains
                "--bind", f"{host_elan}:{container_elan}",
                # Bind the Project folder to /work
                "--bind", f"{host_project}:{container_work}",
                # Set CWD to /work so 'lake' finds lakefile.lean
                "--pwd", container_work,
                # Environment Setup
                "--env", f"ELAN_HOME={container_elan}/.elan_data",
                "--env", f"PATH={container_elan}/lean_bin/bin:$PATH",
                str(image),
                # The actual command: use lake to setup env, then run lean on the file
                "lake", "env", "lean", source_file_path.name
            ]
            return cmd
        
        elif self.method == "local":
            # Simple local fallback
            return ["lean", str(source_file_path)]
            
        else:
            raise NotImplementedError(f"Method {self.method} not implemented for Lean")

    def verify(self, source: str, spec: str, filename: Optional[str] = None, **kwargs: Any) -> Dict[str, Any]:
        """Verify the source code using Lean."""
        
        # 1. Determine Location
        # Crucial: We must write the file INTO the project directory so imports work.
        if self.method == "apptainer":
            project_path = Path(self.lean_cfg.get("apptainer", {}).get("project_path"))
        else:
            project_path = Path(".") # Local fallback
            
        ts = int(time.time() * 1000)
        safe_name = (filename or "submission").replace("/", "_")
        out_name = f"{safe_name}_{ts}.lean"
        
        # The file is written to the host's project folder
        out_path = project_path / out_name
        
        # 2. Write File
        try:
            out_path.write_text(source)
        except Exception as e:
            return {"ok": False, "reason": f"Write Error: {e}", "raw": None, "file": str(out_path)}

        # 3. Build Command
        try:
            cmd = self._build_command(out_path)
        except Exception as e:
            return {"ok": False, "reason": f"Config Error: {e}", "raw": None, "file": str(out_path)}

        # 4. Execute
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=self.timeout)
            
            stdout = proc.stdout
            stderr = proc.stderr
            rc = proc.returncode
            
            raw = {"stdout": stdout, "stderr": stderr, "returncode": rc}
            
            # Lean logic:
            # Usually exit code 0 is success. 
            # Output might contain "error:" strings even if rc=1 (or sometimes 0 in older versions).
            ok = (rc == 0)
            reason = None
            
            if not ok:
                reason = "Lean exited with error code"
                if stderr:
                    reason += f": {stderr[:200]}..."
                elif stdout:
                    reason += f": {stdout[:200]}..."
            
            return {"ok": ok, "reason": reason, "raw": raw, "file": str(out_path)}

        except subprocess.TimeoutExpired:
            return {"ok": False, "reason": f"Timeout after {self.timeout}s", "raw": None, "file": str(out_path)}
        except Exception as e:
            return {"ok": False, "reason": f"Execution Error: {e}", "raw": None, "file": str(out_path)}