import Mathlib

/-- Reflected Gray code adjacency: the codewords `gray t = t ^^^ t / 2` and `gray (t + 1)` differ in
exactly one bit, i.e. their XOR is a power of two. In the positional GGH15 WE candidate of the note
`pq-we-ggh15-chain-verdict`, this is why consecutive hybrids differ in one level only. -/
theorem AdvancedEncryption.WE.Gray.adjacent_one_bit (t : ℕ) :
    ∃ j : ℕ, (t ^^^ t / 2) ^^^ ((t + 1) ^^^ (t + 1) / 2) = 2 ^ j := by sorry
