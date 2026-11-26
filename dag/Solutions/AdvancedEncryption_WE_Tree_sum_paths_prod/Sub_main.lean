import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem solution {R : Type*} [Semiring R] (d : ℕ)
    (f : Fin d → Bool → R) :
    (List.ofFn fun i => f i false + f i true).prod =
      ∑ α : Fin d → Bool, (List.ofFn fun i => f i (α i)).prod := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => f i.succ)]
    rw [← (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_mul, Finset.mul_sum, Finset.mul_sum]
    simp [Fin.consEquiv, List.ofFn_succ, add_comm]
