import Mathlib

/-- Noisy gadget encodings of one value are uniquely decodable. If `d = x - x'` is the difference
of two values whose encodings `y_b = 2^b x + e_b (mod 2^k)`, `b < k`, coincide up to errors whose
differences `r_b` satisfy `|r_b| < 2^(k-1)` (for example `|e_b|, |e'_b| < 2^(k-2)`), then
`x ≡ x' (mod 2^k)`. This is the attack on the gadget-coefficient repair of the "rank gap as an
LWE-dimension gap" WE candidate in the note `pq-we-repairs-collision-rank-gap`: publishing
`2^b · P M_j s + e` for all `b` reveals `P M_j s`. -/
theorem AdvancedEncryption.WE.Repair.gadget_decode_unique (k : ℕ) (d : ℤ)
    (h : ∀ b < k, ∃ r : ℤ, |r| < 2 ^ (k - 1) ∧ (2 : ℤ) ^ k ∣ 2 ^ b * d - r) :
    (2 : ℤ) ^ k ∣ d := by sorry
