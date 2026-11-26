module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Geometry

set_option autoImplicit true

public section

namespace SigabaNeo.PolyQ

/-- A shell in a gap of the integer squared-length spectrum misses the entire set. -/
theorem shell_empty_of_sq_gap {E : Type*} [Norm E] (L : Set E)
    (hint : ∀ x ∈ L, ∃ j : ℤ, ‖x‖ ^ 2 = (j : ℝ))
    {a b : ℝ} {k : ℤ} (ha : 0 ≤ a) (hlo : (k : ℝ) < a ^ 2)
    (hhi : b ^ 2 < (k : ℝ) + 1) :
    L ∩ {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hax, hxb⟩
  obtain ⟨j, hj⟩ := hint x hx
  have h₁ := hlo.trans_le (pow_le_pow_left₀ ha hax 2)
  have h₂ := (pow_le_pow_left₀ (ha.trans hax) hxb 2).trans_lt hhi
  rw [hj] at h₁ h₂
  have hk : k < j := by exact_mod_cast h₁
  have hjk : j < k + 1 := by exact_mod_cast h₂
  omega

#print axioms shell_empty_of_sq_gap

end SigabaNeo.PolyQ
