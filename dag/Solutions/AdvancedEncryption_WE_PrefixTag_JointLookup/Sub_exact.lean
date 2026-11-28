import Mathlib

theorem solution {I : Type*} (a b : I → Prop) [DecidablePred b] (hd : ∀ i, a i → ¬ b i)
    (r : I → Bool) (m : Bool) :
    let r' := fun i => if b i then !(r i) else r i
    (∀ i, a i → r' i = r i) ∧
    (∀ i, b i → Bool.xor (r' i) (!m) = Bool.xor (r i) m) ∧
    (∀ i, (if b i then !(r' i) else r' i) = r i) := by
  dsimp only
  constructor
  · intro i ha
    simp [hd i ha]
  constructor
  · intro i hb
    simp only [hb, ↓reduceIte]
    cases r i <;> cases m <;> decide
  · intro i
    by_cases h : b i <;> simp [h]
