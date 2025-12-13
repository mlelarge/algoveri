from src.eval.lean_eval import LeanEval


class MockLLM:
    def __init__(self, response: str):
        self.response = response

    def chat(self, messages):
        # returns assistant text
        return self.response


class MockVerifier:
    def __init__(self, ok=True):
        self.ok = ok

    def verify(self, source: str):
        # simple stub: return ok if 'theorem' in source
        if self.ok or 'theorem' in source:
            return {"ok": True, "message": "verified"}
        return {"ok": False, "message": "error: missing theorem"}


def demo():
    sample_response = """Here is a solution:

```lean
theorem trivial : True := by
  trivial
```
"""
    llm = MockLLM(sample_response)
    verifier = MockVerifier(ok=True)
    evalr = LeanEval(llm_client=llm, verifier=verifier)
    res = evalr.run_single("Prove True")
    print("Verified:", res.verified)
    print("Details:", res.details)


if __name__ == '__main__':
    demo()
