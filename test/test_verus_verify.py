from pathlib import Path

from src.verifiers.verus_verifier import VerusVerifier

code = """use vstd::prelude::*;

verus! {

    pub struct Stack {
        // The physical storage
        pub elems: Vec<i32>,
    }

    impl Stack {
        // INVARIANT:
        // This 'spec' function defines what a valid stack looks like.
        // It acts as a constraint that must always be true before and after every method.
        pub open spec fn is_well_formed(&self) -> bool {
            // 1. The stack must always contain non-negative numbers (per your requirement)
            forall |i: int| 0 <= i < self.elems.len() ==> self.elems[i] >= 0
        }

        // The View (@) represents the mathematical sequence of the stack
        pub open spec fn view(&self) -> Seq<i32> {
            self.elems@
        }

        pub fn new() -> (s: Self)
            ensures
                s.is_well_formed(),
                s.view().len() == 0,
        {
            Stack { elems: Vec::new() }
        }

        // PUSH SPECIFICATION
        pub fn push(&mut self, val: i32)
            requires
                old(self).is_well_formed(),
                val >= 0,
            ensures
                self.is_well_formed(),
                // LIFO PART 1: The new stack is the old stack + 'val' at the VERY END
                self.view() == old(self).view().push(val),
        {
            self.elems.push(val);
            proof {
                assert(forall |i: int| 0 <= i < self.elems.len() ==> self.elems[i] >= 0);
            }
        }

        // POP SPECIFICATION
        pub fn pop(&mut self) -> (ret: i32)
            requires
                old(self).is_well_formed(),
            ensures
                self.is_well_formed(),
                // Case A: Empty Stack
                old(self).view().len() == 0 ==> (
                    ret == -1 && self.view() == old(self).view()
                ),
                // Case B: Non-Empty (The LIFO definition)
                old(self).view().len() > 0 ==> (
                    // LIFO PART 2: Return value MUST be the last element
                    ret == old(self).view().last() &&
                    // LIFO PART 3: The stack MUST be the old stack without that last element
                    self.view() == old(self).view().drop_last()
                ),
        {
            match self.elems.pop() {
                Some(v) => v,
                None => -1,
            }
        }
    }

    // ==========================================================
    // PROOF OF LIFO PROPERTY
    // ==========================================================
    
    fn prove_lifo_property(mut s: Stack, val: i32)
        requires 
            s.is_well_formed(),
            val >= 0,
    {
        // FIX: We use 'let ghost' to capture the state.
        // This tells Verus: "This variable is for verification only, do not compile it."
        let ghost original_state = s.view();

        // 1. Push the value (Executes at runtime)
        s.push(val);

        // 2. Pop the value (Executes at runtime)
        let ret = s.pop();

        // 3. Verify the "Round Trip"
        assert(ret == val);
        
        // We can compare the current view against our ghost variable
        assert(s.view() == original_state); 
    }

    fn main() {
        let mut s = Stack::new();
        s.push(10);
        s.push(20);
        
        // We can call our proof function as a check
        prove_lifo_property(s, 5);
    }
}"""

def test_verus_verifier_writes_file_and_returns_result():
    """Verify that VerusVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    It does not require a working `verus` binary; it only asserts that the
    verifier produces a dict with expected keys and that the output file exists.
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = VerusVerifier(config_path=str(cfg_path))

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
    test_verus_verifier_writes_file_and_returns_result()
