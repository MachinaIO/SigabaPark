import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Common

theorem solution {K X : Type*} [Field K] (ν : K → X) (hν : Function.Injective ν) (τ : K) :
    (∀ a b : K, (∀ x y : K, ν ((x + a) + (y + b) * τ) = ν (x + y * τ)) ↔ a + b * τ = 0) ∧
      ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → a + b * τ = 0 → b ≠ 0 ∧ τ = -a / b := by
  refine ⟨fun a b => ⟨fun h => ?_, fun h x y => ?_⟩, fun a b hne h => ?_⟩
  · have := hν (h 0 0)
    linear_combination this
  · congr 1
    linear_combination h
  · have hb : b ≠ 0 := by
      rintro rfl
      rcases hne with ha | hb
      · exact ha (by simpa using h)
      · exact hb rfl
    refine ⟨hb, ?_⟩
    field_simp
    linear_combination h
