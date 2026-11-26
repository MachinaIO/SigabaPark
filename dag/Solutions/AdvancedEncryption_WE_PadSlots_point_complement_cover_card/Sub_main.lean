import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common

theorem solution {n : ℕ} {ι : Type*} [Fintype ι] (C : ι → Fin n → Option Bool)
    (p : Fin n → Bool)
    (hp : ∀ j, ¬ ∀ i, C j i = none ∨ C j i = some (p i))
    (hcov : ∀ x : Fin n → Bool, x ≠ p → ∃ j, ∀ i, C j i = none ∨ C j i = some (x i)) :
    n ≤ Fintype.card ι := by
  classical
  let x : Fin n → Fin n → Bool := fun i => Function.update p i (!p i)
  have hx : ∀ i, x i ≠ p := by
    intro i h
    have := congrFun h i
    simp [x] at this
  choose f hf using fun i => hcov (x i) (hx i)
  have key : ∀ i, C (f i) i = some (!p i) := by
    intro i
    by_contra hne
    apply hp (f i)
    intro l
    rcases hf i l with h | h
    · exact Or.inl h
    · by_cases hl : l = i
      · subst hl
        simp [x] at h
        exact absurd h hne
      · right
        simpa [x, Function.update_of_ne hl] using h
  have inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h1 := key i
    rw [hij] at h1
    rcases hf j i with h | h
    · rw [h1] at h
      simp at h
    · rw [h1] at h
      simp [x, Function.update_of_ne hne] at h
  simpa using Fintype.card_le_of_injective f inj
