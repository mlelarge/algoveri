"""Stubbed Dafny verifier adapter."""
from .base import BaseVerifier
from typing import Dict, Any


class DafnyVerifier(BaseVerifier):
    def __init__(self, dafny_bin: str = "dafny"):
        self.dafny_bin = dafny_bin

    def verify(self, source: str, spec: str, **kwargs: Any) -> Dict[str, Any]:
        # For now, we don't shell out; we return a structured stub.
        return {"ok": False, "reason": "dafny verifier not implemented", "raw": None}
