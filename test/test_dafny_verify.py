from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// <preamble>
datatype Tree = Empty | Node(val: int, left: Tree, right: Tree)

function view(tree: Tree): set<int>
    decreases tree
{
    match tree
    case Empty => {}
    case Node(val, left, right) => view(left) + view(right) + {val}
}

predicate is_bst(tree: Tree)
    decreases tree
{
    match tree
    case Empty => true
    case Node(val, left, right) =>
        (forall x :: x in view(left) ==> x < val) &&
        is_bst(left) &&
        (forall x :: x in view(right) ==> x > val) &&
        is_bst(right)
}
// </preamble>

// <helpers>

// </helpers>

// <proofs>

// </proofs>

// <spec>
method zig_zag(g: Tree) returns (res: Tree)
    // g corresponds to Box<Node>, so it is non-Empty
    requires g.Node?
    // g.left is Some (P exists)
    requires g.left.Node?
    // g.left.right is Some (X exists - the 'Zig-Zag' shape)
    requires g.left.right.Node?
    requires is_bst(g)
    ensures is_bst(res)
    ensures view(res) == view(g)
    // X (the original grandchild) is now the root
    ensures res.val == g.left.right.val
// </spec>
// <code>
{
    // Use {:axiom} to suppress warnings about missing proofs
    assume {:axiom} false;
}
// </code>"""

def test_dafny_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = DafnyVerifier(config_path=str(cfg_path))

    sample_source = code
    result = verifier.verify(source=sample_source, spec="", filename="unit_test")

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
