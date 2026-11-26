import Mathlib.Data.Nat.Basic

theorem solution (m j s e : ℕ) (hs : s ≤ e) :
    (∃ a u t : ℕ, a + u + t = m ∧ a ≤ e ∧ u ≤ j * (e - s) ∧ s + t ≤ 2 * e) ↔
      m + (j + 1) * s ≤ (j + 3) * e := by
  have heq : j * e = j * (e - s) + j * s := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hs]
  simp only [Nat.add_mul, Nat.one_mul]
  constructor
  · rintro ⟨a,u,t,hm,ha,hu,ht⟩
    omega
  · intro h
    refine ⟨min m e, min (m - min m e) (j * (e-s)),
      m - min m e - min (m - min m e) (j * (e-s)), ?_⟩
    omega
