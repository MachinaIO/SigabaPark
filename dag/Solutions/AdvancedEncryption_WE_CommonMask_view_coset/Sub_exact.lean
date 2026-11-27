import Mathlib

theorem solution {K R E : Type} [AddCommGroup K] [AddCommGroup R] [AddCommGroup E]
    (restrict : K →+ R) (aggregate : K →+ E) (unit : E) :
    (∀ k, ∃ k', restrict k' = restrict k ∧ aggregate k' = aggregate k + unit) ↔
    ∃ u, restrict u = 0 ∧ aggregate u = unit := by
  constructor
  · intro h
    obtain ⟨u,hr,ha⟩ := h 0
    exact ⟨u,by simpa using hr,by simpa using ha⟩
  · rintro ⟨u,hr,ha⟩ k
    exact ⟨k+u,by simp [hr],by simp [ha]⟩
