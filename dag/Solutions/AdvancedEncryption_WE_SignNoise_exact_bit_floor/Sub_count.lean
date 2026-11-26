import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

theorem solution (m d b : ℕ) (emit : (Fin b → Bool) → Fin d → ℕ)
    (matchAtom :
      (Finset.univ.filter (fun t : Fin b → Bool ↦ ∀ j, emit t j = m)).card *
        Fintype.card (Fin d → Finset (Fin m)) =
      (Finset.univ.filter (fun t : Fin d → Finset (Fin m) ↦ ∀ j, (t j).card = m)).card *
        Fintype.card (Fin b → Bool)) : m * d ≤ b := by
  classical
  have he : (Finset.univ.filter (fun t : Fin d → Finset (Fin m) ↦ ∀ j, (t j).card = m)) =
      {fun _ ↦ Finset.univ} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext j
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using (h j).ge)
    · rintro rfl j
      simp
  rw [he] at matchAtom
  simp only [Finset.card_singleton, one_mul, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_finset, ← pow_mul] at matchAtom
  have hp : 0 < (2:ℕ)^b := by positivity
  have hc : 0 < (Finset.univ.filter (fun t : Fin b → Bool ↦ ∀ j, emit t j = m)).card := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_mul] at matchAtom
    omega
  have hm : (2:ℕ)^(m*d) ≤ 2^b := by
    rw [← matchAtom]
    exact Nat.le_mul_of_pos_left _ hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hm
