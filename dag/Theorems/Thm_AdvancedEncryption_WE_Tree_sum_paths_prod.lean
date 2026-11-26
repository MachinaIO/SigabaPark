import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem AdvancedEncryption.WE.Tree.sum_paths_prod {R : Type*} [Semiring R] (d : ℕ)
    (f : Fin d → Bool → R) :
    (List.ofFn fun i => f i false + f i true).prod =
      ∑ α : Fin d → Bool, (List.ofFn fun i => f i (α i)).prod := by sorry
