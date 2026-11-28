import Mathlib

theorem AdvancedEncryption.WE.SuccinctPacket.diagonal_slice {K I B : Type} [Field K] [Fintype B] [DecidableEq I]
    (V : Submodule K (I → K)) (l r : B → I → K) (hr : ∀ b, r b ∈ V)
    (p : I → K) (h : ∀ i j, (if i = j then p i else 0) = ∑ b, l b i * r b j)
    (i : I) (hi : p i ≠ 0) : (fun j => if i = j then (1:K) else 0) ∈ V := by sorry
