import Mathlib

theorem solution {I : Type} (s : Finset I) (q : I → Bool) :
    let sign := fun i => if q i then (-1 : ℤ) else 1
    let total := ∑ t ∈ s.powerset, ∏ i ∈ t, sign i
    ((∀ i ∈ s, q i = false) → total = (2 : ℤ) ^ s.card) ∧
    ((∃ i ∈ s, q i = true) → total = 0) := by
  classical
  dsimp only
  let sign := fun i => if q i then (-1 : ℤ) else 1
  have expand : (∑ t ∈ s.powerset, ∏ i ∈ t, sign i) = ∏ i ∈ s, (sign i + 1) := by
    simpa using (Finset.prod_add sign (fun _ => (1 : ℤ)) s).symm
  change ((∀ i ∈ s, q i = false) → (∑ t ∈ s.powerset, ∏ i ∈ t, sign i) = _) ∧
    ((∃ i ∈ s, q i = true) → (∑ t ∈ s.powerset, ∏ i ∈ t, sign i) = 0)
  rw [expand]
  constructor
  · intro h
    calc
      _ = ∏ _i ∈ s, (2 : ℤ) := Finset.prod_congr rfl (fun i hi => by simp [sign,h i hi])
      _ = _ := by simp
  · rintro ⟨i,hi,yes⟩
    exact Finset.prod_eq_zero hi (by simp [sign,yes])
