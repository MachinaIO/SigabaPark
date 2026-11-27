import Mathlib

theorem solution {V : Type} [DecidableEq V] (S : Finset V) (terms : Finset (Finset V))
    (proper : ∀ T ∈ terms, T ⊂ S) (coeff : Finset V → ZMod 2) :
    let eval := fun U : Finset V ↦ ∑ T ∈ terms, if T ⊆ U then coeff T else 0
    eval S ≠ 0 → ∃ U, U ⊂ S ∧ eval U ≠ 0 := by
  classical
  dsimp only
  intro top
  have hz (T : Finset V) (ht : T ∈ terms) :
      (∑ U ∈ S.powerset, if T ⊆ U then coeff T else 0) = 0 := by
    rw [← Finset.sum_filter, ← Finset.Icc_eq_filter_powerset,
      Finset.sum_const, Finset.card_Icc_finset (proper T ht).le]
    have hlt := Finset.card_lt_card (proper T ht)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show S.card-T.card ≠ 0 by omega)
    rw [hk, pow_succ, mul_nsmul]
    simp [show (2 : ZMod 2) = 0 by decide]
  have hsum : (∑ U ∈ S.powerset, ∑ T ∈ terms, if T ⊆ U then coeff T else 0) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero hz
  by_contra h
  have only : ∀ U ∈ S.powerset, U ≠ S →
      (∑ T ∈ terms, if T ⊆ U then coeff T else 0) = 0 := by
    intro U hu ne
    by_contra non
    exact h ⟨U,lt_of_le_of_ne (Finset.mem_powerset.1 hu) ne,non⟩
  rw [Finset.sum_eq_single S only (by simp)] at hsum
  exact top hsum
