from pathlib import Path

from src.verifiers.lean_verifier import LeanVerifier

code = "import Mathlib\nset_option maxHeartbeats 0\n\n@[reducible, simp]\ndef goodWorkers_precond (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat) : Prop :=\n  records.length \u2264 4000 \u2227\n  \u2200 r \u2208 records, (r.2.1 \u2264 1_000_000) \u2227 (r.2.2 \u2264 100_000)\n\ndef totalSales (records : List (Nat \u00d7 Nat \u00d7 Nat)) (id : Nat) : Nat :=\n  records.foldl (fun acc r => if r.1 = id then acc + r.2.1 * r.2.2 else acc) 0\n\ndef distinctIds (records : List (Nat \u00d7 Nat \u00d7 Nat)) : List Nat :=\n  records.foldl (fun acc r => if r.1 \u2208 acc then acc else acc ++ [r.1]) []\n\ndef qualifyingIds (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat) : List Nat :=\n  (distinctIds records).filter (fun i => totalSales records i \u2265 threshold)\n\ndef goodWorkers (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (h_precond : goodWorkers_precond records threshold) : List Nat :=\n  qualifyingIds records threshold\n\n@[reducible, simp]\ndef goodWorkers_postcond (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (result : List Nat) (h_precond : goodWorkers_precond records threshold) : Prop :=\n  result = qualifyingIds records threshold\n\nlemma goodWorkers_eq (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (h_precond : goodWorkers_precond records threshold) :\n    goodWorkers records threshold h_precond = qualifyingIds records threshold := by\n  unfold goodWorkers\n  rfl\n\nlemma goodWorkers_postcond_of_eq (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (result : List Nat) (h_precond : goodWorkers_precond records threshold)\n    (h_eq : result = qualifyingIds records threshold) :\n    goodWorkers_postcond records threshold result h_precond := by\n  unfold goodWorkers_postcond\n  simpa [h_eq]\n\ntheorem goodWorkers_postcond_satisfied (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (h_precond : goodWorkers_precond records threshold) :\n    goodWorkers_postcond records threshold (goodWorkers records threshold h_precond) h_precond := by\n  have h_eq := goodWorkers_eq records threshold h_precond\n  exact goodWorkers_postcond_of_eq records threshold\n    (goodWorkers records threshold h_precond) h_precond h_eq"

def test_lean_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = LeanVerifier(config_path=str(cfg_path))

    sample_source = code
    result = verifier.verify(source=sample_source, spec="dummy-spec", filename="unit_test")

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
    test_lean_verifier_writes_file_and_returns_result()
