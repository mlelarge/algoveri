from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// Following is the block for necessary definitions
// <preamble>
// Calculates the total length of the pieces
function sum_lengths(cuts: seq<int>): int
    decreases |cuts|
{
    if |cuts| == 0 then
        0
    else
        cuts[0] + sum_lengths(cuts[1..])
}

// Helper: Safe price lookup that returns 0 for out-of-bounds
function get_price(prices: seq<int>, idx: int): int {
    if 0 <= idx < |prices| then
        prices[idx]
    else
        0
}

// Calculates revenue recursively.
function calculate_revenue(cuts: seq<int>, prices: seq<int>): int
    decreases |cuts|
{
    if |cuts| == 0 then
        0
    else
        // Revenue is price of first piece + revenue of remaining pieces
        get_price(prices, cuts[0] - 1) + 
        calculate_revenue(cuts[1..], prices)
}

// Definition of a valid strategy: positive cuts, valid prices, sums to n
predicate is_valid_strategy(cuts: seq<int>, n: int, prices: seq<int>) {
    (forall i: int :: 0 <= i < |cuts| ==> cuts[i] > 0) &&
    (forall i: int :: 0 <= i < |cuts| ==> cuts[i] - 1 < |prices|) &&
    sum_lengths(cuts) == n
}
// </preamble>

// Following is the block for potential helper specifications
// <helpers>

// </helpers>

// Following is the block for proofs of lemmas
// <proofs>

// </proofs>

// Following is the block for the main specification
// <spec>
method rod_cutting(n: int, prices: seq<int>) returns (result: int)
    requires |prices| >= n
    requires n <= 1000
    // Constraints matching Verus u64/usize unsigned and explicit bounds
    requires forall i: int :: 0 <= i < |prices| ==> 0 <= prices[i] <= 10000
    ensures result >= 0
    // 1. Upper Bound
    ensures forall cuts: seq<int> :: (is_valid_strategy(cuts, n, prices) 
            ==> calculate_revenue(cuts, prices) <= result)
    // 2. Existence
    ensures exists cuts: seq<int> :: (is_valid_strategy(cuts, n, prices) 
            && calculate_revenue(cuts, prices) == result)
// </spec>
// <code>
{
    // Implement and verify the Rod Cutting DP algorithm here.
    assume{:axiom} false;
}
// </code>
"""

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
