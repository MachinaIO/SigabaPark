import Mathlib

theorem AdvancedEncryption.WE.TerminalTokens.ternary_floor (front : List ℕ) (b : ℕ)
    (total : front.sum + b = 128)
    (small : ∀ a ∈ front, a ≤ 25) (hb : b ≤ 25) :
    2^32 ≤ 64 * (front.map (fun a => 2^a)).sum +
      2^b * 3^(2^(front.length-1)-1) := by
  sorry
