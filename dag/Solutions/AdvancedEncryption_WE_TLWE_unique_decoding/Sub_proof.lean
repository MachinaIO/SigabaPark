import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith

theorem solution {m : Type*} (Λ : AddSubgroup (m → ℤ)) (B : ℤ)
    (hΛ : ∀ v ∈ Λ, v ≠ 0 → ∃ i, B ≤ |v i|)
    (δ δ' : m → ℤ) (hsmall : ∀ i, |δ i| + |δ' i| < B) (hmem : δ - δ' ∈ Λ) : δ = δ' := by
  by_contra hne
  obtain ⟨i, hi⟩ := hΛ _ hmem (sub_ne_zero.mpr hne)
  have h1 : |(δ - δ') i| ≤ |δ i| + |δ' i| := by
    simp only [Pi.sub_apply]; exact abs_sub _ _
  linarith [hsmall i]
