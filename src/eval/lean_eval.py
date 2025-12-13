from __future__ import annotations
import re
from typing import Dict, Any

from .base_eval import BaseEval, EvalResult

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

# attempt to import Lean verifier
try:
    from verifiers.lean_verifier import LeanVerifier
except Exception:
    LeanVerifier = None

###############################
# Helper functions for processing prompts
###############################

def parse_response(response: str) -> dict:
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
###############################

class LeanEval(BaseEval):
    def __init__(self, llm_client, verifier=None, max_rounds: int = 5):
        if verifier is None and LeanVerifier is not None:
            verifier = LeanVerifier()
        super().__init__(llm_client=llm_client, verifier=verifier, max_rounds=max_rounds)
    
    def make_sys_prompt(self) -> str:
        return LEAN_SYSTEM_PROMPT

    def make_initial_prompt(self, problem: str) -> str:
            user_p = LEAN_INITIAL_PROMPT.format(formal_problem=problem)
            return user_p
    
    def make_revision_prompt(self, compiler_messages: str) -> str:
        return LEAN_REVISION_PROMPT.format(compiler_error_messages=compiler_messages)

    def parse_llm_response(self, response: str) -> Dict[str, str]:
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

    def postprocess_code(self, code: str) -> str:
        # Basic postprocessing: remove leading/trailing fences or markers
        # and ensure newlines at end
        code = re.sub(r"^```.*\n", "", code)
        code = re.sub(r"\n```$", "", code)
        return code.strip() + "\n"

    def call_verifier(self, code: str) -> EvalResult:
        # Use BaseEval.call_verifier which wraps verifier.verify
        res = super().call_verifier(code)
        # Optionally parse verifier feedback into a friendly structure
        # Many verifiers return dicts; normalize
        details = res.details
        if isinstance(details, dict):
            # try to produce a short message string in details['message']
            if "message" not in details:
                # compose message from keys
                msg = ", ".join(f"{k}: {v}" for k, v in details.items())
                details["message"] = msg
        return EvalResult(verified=res.verified, details=details)

    # run_single inherited from BaseEval is adequate
