import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

theorem AdvancedEncryption.WE.SignNoise.exact_bit_floor (m d b : ℕ) (emit : (Fin b → Bool) → Fin d → ℕ)
    (matchAtom :
      (Finset.univ.filter (fun t : Fin b → Bool ↦ ∀ j, emit t j = m)).card *
        Fintype.card (Fin d → Finset (Fin m)) =
      (Finset.univ.filter (fun t : Fin d → Finset (Fin m) ↦ ∀ j, (t j).card = m)).card *
        Fintype.card (Fin b → Bool)) : m * d ≤ b := by
  sorry
