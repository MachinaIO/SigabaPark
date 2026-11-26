import Mathlib

open Finset in
theorem solution {K : Type*} [Field K] {N d : ℕ} (z : Fin N → Fin d → K) (hN : d + 1 < N) :
    ∃ α : Fin N → K, α ≠ 0 ∧ ∑ j, α j = 0 ∧ ∑ j, α j • z j = 0 := by
  classical
  let v : Fin N → (Option (Fin d) → K) := fun j o => o.elim 1 (z j)
  have hnot : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_option] at this
    omega
  obtain ⟨α, hα, hne⟩ := Fintype.not_linearIndependent_iff.mp hnot
  obtain ⟨i, hi⟩ := hne
  refine ⟨α, fun h => hi (by simp [h]), ?_, ?_⟩
  · have := congrFun hα none
    simpa [v, Finset.sum_apply] using this
  · funext k
    have := congrFun hα (some k)
    simpa [v, Finset.sum_apply] using this
