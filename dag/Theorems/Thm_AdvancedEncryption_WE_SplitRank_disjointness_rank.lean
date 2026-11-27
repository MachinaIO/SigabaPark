import Mathlib.Combinatorics.Colex
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

theorem AdvancedEncryption.WE.SplitRank.disjointness_rank (h : ℕ) :
    let D : Matrix (Finset (Fin h)) (Finset (Fin h)) (ZMod 2) :=
      Matrix.of fun s t ↦ if Disjoint s t then 1 else 0
    IsUnit D ∧ D.rank = 2 ^ h ∧
      ∀ {m n r : ℕ} (U : Matrix (Fin m) (Fin r) (ZMod 2))
        (V : Matrix (Fin r) (Fin n) (ZMod 2))
        (rows : Finset (Fin h) → Fin m) (cols : Finset (Fin h) → Fin n),
        (U * V).submatrix rows cols = D → 2 ^ h ≤ r := by sorry
