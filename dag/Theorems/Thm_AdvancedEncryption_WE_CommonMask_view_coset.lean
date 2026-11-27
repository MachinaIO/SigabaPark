import Mathlib

theorem AdvancedEncryption.WE.CommonMask.view_coset {K R E : Type} [AddCommGroup K] [AddCommGroup R] [AddCommGroup E]
    (restrict : K →+ R) (aggregate : K →+ E) (unit : E) :
    (∀ k, ∃ k', restrict k' = restrict k ∧ aggregate k' = aggregate k + unit) ↔
    ∃ u, restrict u = 0 ∧ aggregate u = unit := by
  sorry
