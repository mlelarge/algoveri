from pathlib import Path

from src.verifiers.verus_verifier import VerusVerifier

code = """use vstd::prelude::*;

verus! {
    // <preamble>
    pub open spec fn spec_pow(b: nat, e: nat) -> nat
        decreases e
    {
        if e == 0 {
            1
        } else {
            b * spec_pow(b, (e - 1) as nat)
        }
    }
    // </preamble>

    // <helpers>

    // </helpers>

    // <proofs>
    // 1. Basic associativity lemma for multiplication
    pub proof fn lemma_mul_assoc(a: nat, b: nat, c: nat)
        ensures (a * b) * c == a * (b * c)
    {
        // Verus non-linear arithmetic can usually handle this specific identity
        // if isolated, but explicit assertion helps.
        assert((a * b) * c == a * (b * c));
    }

    // 2. The core lemma: (b*b)^n == b^(2n)
    pub proof fn lemma_square_pow(b: nat, n: nat)
        ensures spec_pow(b * b, n) == spec_pow(b, (2 * n) as nat)
        decreases n
    {
        if n == 0 {
            // Trivial: 1 == 1
        } else {
            // Inductive step
            // Hyp: spec_pow(b*b, n-1) == spec_pow(b, 2n - 2)
            lemma_square_pow(b, (n - 1) as nat);
            
            // Goal: (b*b) * spec_pow(b*b, n-1) == b * (b * spec_pow(b, 2n-2))
            
            let inner = spec_pow(b, (2 * n - 2) as nat);
            // We know spec_pow(b*b, n-1) == inner (from IH)
            
            // Prove: (b*b) * inner == b * (b * inner)
            lemma_mul_assoc(b, b, inner);
            
            // Connect to definition of spec_pow(b, 2n)
            // spec_pow(b, 2n) = b * spec_pow(b, 2n-1)
            //                 = b * (b * spec_pow(b, 2n-2))
            assert(spec_pow(b, (2 * n) as nat) == b * spec_pow(b, (2 * n - 1) as nat));
            assert(spec_pow(b, (2 * n - 1) as nat) == b * spec_pow(b, (2 * n - 2) as nat));
        }
    }

    // 3. Lemma for overflow safety
    // If x * y == Z and Z <= MAX, then x <= MAX (provided y >= 1)
    pub proof fn lemma_factor_bound(x: nat, y: nat, z: nat, limit: nat)
        requires x * y == z, z <= limit, y >= 1
        ensures x <= limit
    {
        if x > limit {
            // Proof by contradiction
            assert(x * y > limit); 
        }
    }
    // </proofs>

    // <spec>
    fn exponentiation(b: u64, e: u64) -> (res: u64)
        requires
            spec_pow(b as nat, e as nat) <= 0xffff_ffff_ffff_ffff
        ensures
            res == spec_pow(b as nat, e as nat)
    // </spec>
    // <code>
    {
        let mut res: u64 = 1;
        let mut base: u64 = b;
        let mut exp: u64 = e;

        while exp > 0
            invariant
                // 1. Functional Correctness
                res as nat * spec_pow(base as nat, exp as nat) == spec_pow(b as nat, e as nat),
                
                // 2. Safety Bounds
                spec_pow(b as nat, e as nat) <= 0xffff_ffff_ffff_ffff,
                
                // 3. Helper to ensure `res` fits in u64
                // (Since res is a factor of the total result, and base^exp >= 1 if base > 0)
                base > 0 ==> res as nat <= spec_pow(b as nat, e as nat),
                base == 0 ==> res as nat * spec_pow(0, exp as nat) == spec_pow(b as nat, e as nat),
        {
            if exp % 2 != 0 {
                // We need to prove `res * base` doesn't overflow.
                proof {
                    if base > 0 {
                        // total = res * base * base^(exp-1)
                        // Since base >= 1 and exp >= 1, base^(exp-1) >= 1.
                        // Therefore (res * base) <= total <= MAX.
                        let remainder = spec_pow(base as nat, (exp - 1) as nat);
                        // Trigger the inequality check
                        assert((res * base) * remainder == spec_pow(b as nat, e as nat));
                    }
                }
                
                res = res * base;
            }

            // We are about to halve exp.
            // We need to maintain invariant: res * new_base^new_exp == total
            // Current: res * base^exp == total
            // If exp was odd, we did res*=base, so effectively we have base^(exp-1) remaining.
            // (exp-1) is even. (exp-1) = 2 * (exp/2).
            // If exp was even, exp = 2 * (exp/2).
            // In both cases, the power of base remaining is 2 * (exp/2).
            
            // We need to show: base^(2*k) == (base*base)^k
            proof {
                lemma_square_pow(base as nat, (exp / 2) as nat);
            }

            exp = exp / 2;

            if exp > 0 {
                // We need to prove `base * base` doesn't overflow.
                proof {
                    // We know res * (base^2)^exp == total <= MAX
                    // Since exp >= 1, (base^2) is a factor of total.
                    // If total <= MAX, then base^2 <= MAX (assuming res >= 1).
                    if base > 0 { 
                        // If base=0, base*base=0, safe.
                        // If base>0, base^2 >= 1.
                        let rest = spec_pow(base as nat * base as nat, (exp - 1) as nat);
                        // (base*base) * (rest * res) == total
                        // Thus base*base <= total <= MAX
                        assert((base as nat * base as nat) * (rest * res as nat) == spec_pow(b as nat, e as nat));
                    }
                }
                base = base * base;
            }
        }
        res
    }
    // </code>

    fn main() {}
}"""

def test_verus_verifier_writes_file_and_returns_result():
    """Verify that VerusVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    It does not require a working `verus` binary; it only asserts that the
    verifier produces a dict with expected keys and that the output file exists.
    """
    cfg_path = Path(__file__).resolve().parent / "config_jiawei_test.yaml"
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
