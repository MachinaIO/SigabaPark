import Mathlib

theorem solution {Tape : Type*} [DecidableEq Tape] (u : ℕ) (good : (Fin u → Bool) → Finset Tape)
    (n : ℕ) (bound : ∀ y, (good y).card ≤ n) :
    (Finset.univ.biUnion good).card ≤ 2^u*n := by
  have h := Finset.card_biUnion_le_card_mul Finset.univ good n (fun a _ => bound a)
  simpa using h
