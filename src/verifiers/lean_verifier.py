"""Stubbed Lean verifier adapter."""
from .base import BaseVerifier
from typing import Dict, Any


class LeanVerifier(BaseVerifier):
    def __init__(self, lean_bin: str = "lean"):
        self.lean_bin = lean_bin

    def verify(self, source: str, spec: str, **kwargs: Any) -> Dict[str, Any]:
        return {"ok": False, "reason": "lean verifier not implemented", "raw": None}
