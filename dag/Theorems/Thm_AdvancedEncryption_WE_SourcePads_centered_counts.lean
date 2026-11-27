import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.SourcePads.centered_counts {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (C : A → B → ℝ) (N : ℝ) (row : ∀ a, ∑ b, C a b = N) :
    (∑ a, ∑ b, (C a b - N / Fintype.card B)^2) =
    (∑ a, ∑ b, (C a b)^2) - (Fintype.card A : ℝ)*N^2/Fintype.card B := by sorry
