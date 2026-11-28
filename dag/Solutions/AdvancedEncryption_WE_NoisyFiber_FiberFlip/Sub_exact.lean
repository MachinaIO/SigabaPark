import Mathlib

theorem solution {S P T : Type*} [AddCommGroup S] [AddCommGroup P] [AddCommGroup T]
    (A : S →+ P) (c : S →+ T) (d s : S) (e : Bool)
    (half : T) (hd : c d = half) (hh : -half = half) :
    let shift : Bool → S := fun b ↦ if b then d else -d
    let noise : Bool → P := fun b ↦ if b then A d else 0
    A (s + shift e) + noise (!e) = A s + noise e ∧
    c (s + shift e) = c s + half ∧ s + shift e + shift (!e) = s := by
  cases e <;> simp [hd, hh]
