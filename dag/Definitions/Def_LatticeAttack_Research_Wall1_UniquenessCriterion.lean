module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

/-- In the parametrization (h + k • y, k), precisely the origin and the two signed
plants lie in the closed ball of squared radius ‖y‖² + 1 iff the three height tests hold. -/
theorem allHeightsUniquenessCriterion {V : Type*} [NormedAddCommGroup V]
    (H : AddSubgroup V) (y : V) :
    (∀ h ∈ H, ∀ k : ℤ,
      ‖h + k • y‖ ^ 2 + (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 ↔
        h = 0 ∧ (k = 0 ∨ k = 1 ∨ k = -1)) ↔
    (∀ h ∈ H, h ≠ 0 → ‖y‖ ^ 2 + 1 < ‖h‖ ^ 2) ∧
    (∀ h ∈ H, h ≠ 0 → ‖y‖ ^ 2 < ‖h + y‖ ^ 2) ∧
    (∀ k : ℤ, 2 ≤ k → (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 →
      ∀ h ∈ H, ‖y‖ ^ 2 + 1 - (k : ℝ) ^ 2 < ‖h + k • y‖ ^ 2) := by
  constructor
  · intro unique
    refine ⟨?_, ?_, ?_⟩
    · intro h hh hn
      apply lt_of_not_ge
      intro le
      exact hn ((unique h hh 0).mp (by simpa using le)).1
    · intro h hh hn
      apply lt_of_not_ge
      intro le
      exact hn ((unique h hh 1).mp (by simpa using le)).1
    · intro k hk _ h hh
      apply lt_of_not_ge
      intro le
      have heights := ((unique h hh k).mp (by linarith)).2
      omega
  · rintro ⟨zeroTest, oneTest, highTest⟩
    have positive : ∀ h ∈ H, ∀ k : ℤ, 0 ≤ k →
        ‖h + k • y‖ ^ 2 + (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 →
        h = 0 ∧ (k = 0 ∨ k = 1) := by
      intro h hh k hk le
      by_cases e : k = 0
      · subst k
        exact ⟨by
          by_contra hn
          exact (zeroTest h hh hn).not_ge (by simpa using le), Or.inl rfl⟩
      by_cases e₁ : k = 1
      · subst k
        exact ⟨by
          by_contra hn
          exact (oneTest h hh hn).not_ge (by simpa using le), Or.inr rfl⟩
      have bound : (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 := by linarith [sq_nonneg ‖h + k • y‖]
      have strict := highTest k (by omega) bound h hh
      exfalso
      linarith
    intro h hh k
    constructor
    · intro le
      by_cases hk : 0 ≤ k
      · obtain ⟨hz, heights⟩ := positive h hh k hk le
        exact ⟨hz, by omega⟩
      · have reflected := positive (-h) (H.neg_mem hh) (-k) (by omega)
          (by rw [neg_smul, ← neg_add, norm_neg, Int.cast_neg, neg_sq]; exact le)
        exact ⟨neg_eq_zero.mp reflected.1, by have := reflected.2; omega⟩
    · rintro ⟨rfl, rfl | rfl | rfl⟩ <;> simp
      linarith [sq_nonneg ‖y‖]

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.allHeightsUniquenessCriterion
