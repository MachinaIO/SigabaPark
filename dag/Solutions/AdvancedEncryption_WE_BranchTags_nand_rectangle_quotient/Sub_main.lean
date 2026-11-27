import Mathlib.Tactic.Abel

theorem solution
    {G : Type*} [AddCommGroup G] (a b : Bool → Bool → G) :
    (∃ r c : Bool → G, ∀ i j, a i j = b i j + r i + c j) ↔
      a false false - a false true - a true false + a true true =
      b false false - b false true - b true false + b true true := by
  constructor
  · rintro ⟨r, c, h⟩
    simp only [h]
    abel
  · intro h
    refine ⟨fun i ↦ a i false - b i false,
      fun j ↦ a false j - b false j - (a false false - b false false), ?_⟩
    intro i j
    change a i j = b i j + (a i false - b i false) +
      (a false j - b false j - (a false false - b false false))
    cases i <;> cases j
    · abel
    · abel
    · abel
    · calc
       a true true = (a false false - a false true - a true false + a true true) +
          (a false true + a true false - a false false) := by abel
       _ = _ := by rw [h]; abel
