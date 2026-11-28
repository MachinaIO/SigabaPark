import Mathlib

theorem solution {W : Type} [Fintype W] (ok : W → Bool) (t : Nat) (m : Bool) :
    Nat.card {p : (Fin t → W) × Bool //
      (∀ i, ok (p.1 i) = false) ∧ p.2 ≠ m} =
      Nat.card {x : W // ok x = false} ^ t := by
  classical
  let e : {p : (Fin t → W) × Bool // (∀ i, ok (p.1 i) = false) ∧ p.2 ≠ m} ≃
      (Fin t → {x : W // ok x = false}) := {
    toFun := fun p i => ⟨p.val.1 i, p.property.1 i⟩
    invFun := fun y => ⟨(fun i => (y i).val, !m),
      fun i => (y i).property, by change (!m) ≠ m; cases m <;> decide⟩
    left_inv := by
      rintro ⟨⟨xs,b⟩,hx,hb⟩
      change b ≠ m at hb
      apply Subtype.ext
      cases m <;> cases b <;> simp_all
    right_inv := by intro y; rfl }
  simpa using Nat.card_congr e
