from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// <preamble>
<<<<<<< HEAD
// Recursive definition of Modular Exponentiation: (b^e) % m
function spec_pow_mod(b: int, e: int, m: int): int
  decreases e
  requires m > 1
{
  if e <= 0 then
    1
  else
    (b * spec_pow_mod(b, e - 1, m)) % m
}

// The predicate that defines a valid Discrete Logarithm x
predicate is_discrete_log(g: int, h: int, p: int, x: int)
  requires p > 1
{
  spec_pow_mod(g, x, p) == h
=======
// Definition of a Palindrome:
// A sequence is a palindrome if for every index i, the character at i
// is identical to the character at the symmetric position from the end.
predicate is_palindrome(s: seq<int>) {
    // We trigger on s[i] so the solver knows to use this rule 
    // whenever it sees an access to s at index i.
    forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

// Helper to check validity of a subrange within a larger sequence.
predicate is_valid_subrange(s: seq<int>, start: int, len: int) {
    && 0 <= start
    && 0 <= len
    && start + len <= |s|
>>>>>>> ea54b6fa240f351bf8892894d9bb533d15b6eac9
}
// </preamble>

// <helpers>

// </helpers>

// <proofs>

// </proofs>

// <spec>
<<<<<<< HEAD
// Dafny uses a datatype for Option
datatype Option<T> = Some(value: T) | None

method discrete_log_naive(g: int, h: int, p: int) returns (res: Option<int>)
  // Simulate u64: inputs are non-negative
  requires g >= 0 && h >= 0 && p >= 0
  requires p > 1
  
  ensures match res
    case Some(x) => 
      // 1. It is a valid solution
      is_discrete_log(g, h, p, x) &&
      // 2. It is within bounds
      0 <= x < p &&
      // 3. It is the *smallest* solution
      (forall k :: 0 <= k < x ==> !is_discrete_log(g, h, p, k))
    case None =>
      // We assert that NO solution exists in the range [0, p)
      forall k :: 0 <= k < p ==> !is_discrete_log(g, h, p, k)
// </spec>
// <code>
{
  // Implement and verify the naive algorithm to compute the discrete logarithm
  assume {:axiom} false;
}
// </code>

method Main() {
}"""
=======
// The main verification target.
// Returns a tuple (start_index, length) representing the longest palindrome.
method longest_palindromic_substring(s: seq<int>) returns (res: (int, int))
    requires
        // CONSTRAINT: Hard limit of 1,000,000. 
        // Even with Manacher's expansion (2*N + 1), the required size 
        // is ~2,000,001, which fits easily in u32/usize.
        |s| <= 1000000
    ensures
        // Type Constraint: Results must be non-negative (simulating usize)
        res.0 >= 0 && res.1 >= 0
    ensures
        // 1. The result defines a valid substring of the input.
        is_valid_subrange(s, res.0, res.1)
    ensures
        // 2. The substring found is indeed a palindrome.
        is_palindrome(s[res.0 .. res.0 + res.1])
    ensures
        // 3. Maximality: There exists no other valid palindromic substring 
        // with a length strictly greater than the result found.
        forall i, len :: 
            is_valid_subrange(s, i, len) && is_palindrome(s[i .. i + len])
            ==> len <= res.1
// </spec>
// <code>
{
    assume {:axiom} false;
    // Implementation of Manacher's algorithm (or other solution) goes here.
}
// </code>"""
>>>>>>> ea54b6fa240f351bf8892894d9bb533d15b6eac9

def test_dafny_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = DafnyVerifier(config_path=str(cfg_path))

    sample_source = code
    result = verifier.verify(source=sample_source, spec="test", filename="unit_test")

    print(result)

    assert isinstance(result, dict)
    assert "ok" in result and isinstance(result["ok"], bool)
    assert "file" in result

    # The file should have been created on disk
    written = Path(result["file"])
    assert written.exists()
    return
    # cleanup artifact
    try:
        written.unlink()
    except Exception:
        pass

if __name__ == '__main__':
    test_dafny_verifier_writes_file_and_returns_result()
