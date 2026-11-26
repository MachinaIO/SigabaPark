import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

theorem AdvancedEncryption.WE.TLWE.unique_decoding {m : Type*} (Λ : AddSubgroup (m → ℤ)) (B : ℤ)
    (hΛ : ∀ v ∈ Λ, v ≠ 0 → ∃ i, B ≤ |v i|)
    (δ δ' : m → ℤ) (hsmall : ∀ i, |δ i| + |δ' i| < B) (hmem : δ - δ' ∈ Λ) : δ = δ' := by sorry
