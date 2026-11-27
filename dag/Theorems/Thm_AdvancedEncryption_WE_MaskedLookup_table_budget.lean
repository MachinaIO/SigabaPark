import Mathlib
open scoped BigOperators

theorem AdvancedEncryption.WE.MaskedLookup.table_budget (front : List ℕ) (b : ℕ)
    (total : front.sum+b=128) (sizes : ∀ k ∈ front, k ≤ 25) (last : b ≤ 25) :
    (2:ℕ)^32 ≤ 2^b * 4^(2^(front.length-1)-1) := by sorry
