import Mathlib
theorem solution (p d : ℕ) (hp : p.Prime) (hd : 0 < d) (a : ℕ) :
    (d*p ∣ d*a ↔ p ∣ a) ∧ (¬ p ∣ a → Nat.gcd (d*p) (d*a) = d) := by
  constructor
  · exact Nat.dvd_of_mul_dvd_mul_left hd |> fun h ↦ ⟨h, Nat.mul_dvd_mul_left d⟩
  · intro h
    rw [Nat.gcd_mul_left, (Nat.Prime.coprime_iff_not_dvd hp).2 h, Nat.mul_one]
