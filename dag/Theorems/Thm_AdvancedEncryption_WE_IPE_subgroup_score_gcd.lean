import Mathlib
theorem AdvancedEncryption.WE.IPE.subgroup_score_gcd (p d : ℕ) (hp : p.Prime) (hd : 0 < d) (a : ℕ) :
    (d*p ∣ d*a ↔ p ∣ a) ∧ (¬ p ∣ a → Nat.gcd (d*p) (d*a) = d) := by sorry
