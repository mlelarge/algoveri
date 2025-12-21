from __future__ import annotations
import re
from typing import Dict, Any

from .base_eval import BaseEval

# import prompts
from .prompt.lean_prompt import *

# try to provide a prompt helper module if available
try:
    from .prompt import lean_prompt_helper as prompt_helper
except Exception:
    try:
        from src.eval.prompt import lean_prompt_helper as prompt_helper
    except Exception:
        prompt_helper = None

# attempt to import Lean verifier (relative import)
try:
    from ..verifiers.lean_verifier import LeanVerifier
except Exception:
    try:
        from verifiers.lean_verifier import LeanVerifier
    except Exception:
        LeanVerifier = None


class LeanEval(BaseEval):
    def __init__(self, llm_client, verifier=None, max_rounds: int = 5):
        if verifier is None and LeanVerifier is not None:
            verifier = LeanVerifier()
        super().__init__(llm_client=llm_client, verifier=verifier, max_rounds=max_rounds)
    
    def make_sys_prompt(self) -> str:
        return LEAN_SYSTEM_PROMPT

    def make_initial_prompt(self, natural_language, formal_code) -> str:
            user_p = LEAN_INITIAL_PROMPT.format(natural_language=natural_language, formal_code=formal_code)
            return user_p
    
    def make_revision_prompt(self, compiler_messages: str, formal_code: str = None) -> str:
        return LEAN_REVISION_PROMPT.format(compiler_error_messages=compiler_messages)

    def parse_llm_response(self, response: str, formal_code: str = None) -> Dict[str, str]:
        code = ""
        comment = response
        # Prefer ```lean4``` then ```lean``` fenced blocks
        m = re.search(r"```\s*lean4\s*(.*?)```", response, re.S | re.I)
        if not m:
            m = re.search(r"```\s*lean\s*(.*?)```", response, re.S | re.I)

        if m:
            code = m.group(1).strip()
            comment = (response[:m.start()] + response[m.end():]).strip()
        else:
            m2 = re.search(r"```(.*?)```", response, re.S | re.I)
            if m2:
                code = m2.group(1).strip()
                comment = (response[:m2.start()] + response[m2.end():]).strip()
        return {"code": code, "comment": comment}

    def parse_verifier_response(self, response: Dict[str, Any]) -> Dict[str, Any]:
        if not isinstance(response, dict):
            return {"verified": False, "feedback": "Response is not a dict.", "raw": None}
        if "ok" not in response:
            return {"verified": False, "feedback": "Response missing 'ok' field.", "raw": None}
        ok = response["ok"]
        raw = response.get("raw", None)
        if not ok:
            if not raw:
                reason = response.get("reason", "No reason provided.")
                return {"verified": False, "feedback": reason, "raw": None}
            else:
                stdout_message = raw.get("stdout", "")
                stderr_message = raw.get("stderr", "")
                feedback_msg = f"Stdout:\n{stdout_message}\n\nStderr:\n {stderr_message}"
                return {"verified": False, "feedback": feedback_msg, "raw": raw}
        sorry_msg = "declaration uses 'sorry'"
        if not raw:
            return {"verified": False, "feedback": "Bug in verifier.", "raw": None}
        stdout_message = raw.get("stdout", "")
        stderr_message = raw.get("stderr", "")
        if sorry_msg in stdout_message or sorry_msg in stderr_message:
            feedback_msg = "The proof contains 'sorry'.\nStdout:\n{stdout_message}\n\nStderr:\n {stderr_message}"
            return {"verified": False, "feedback": feedback_msg, "raw": raw}

        return {"verified": True, "feedback": "Verified successfully.", "raw": raw}

