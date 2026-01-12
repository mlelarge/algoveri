// Following is the block for necessary definitions
// <preamble>
// Define u64 to enforce the safety constraint (overflow checks)
newtype u64 = x | 0 <= x < 0x1_0000_0000_0000_0000

// Pure mathematical definition of power on unbounded integers
function spec_pow(b: int, e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then
    1
  else
    b * spec_pow(b, e - 1)
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
method exponentiation(b: u64, e: u64) returns (res: u64)
  // Precondition: Result fits in u64 (0xffff_ffff_ffff_ffff)
  requires spec_pow(b as int, e as int) <= 0xffff_ffff_ffff_ffff
  
  ensures res as int == spec_pow(b as int, e as int)
// </spec>
// <code>
{
  // Implement and verify the algorithm to compute the exponential with complexity O(log e)
}
// </code>

method Main() {
  // Empty main
}