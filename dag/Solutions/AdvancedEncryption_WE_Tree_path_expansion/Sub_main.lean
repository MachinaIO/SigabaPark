import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem solution {R : Type*} [Ring R] (H P Q K : ℕ → R)
    (Z : R) (hstep : ∀ j, H j * P j - Z * Q j = H (j + 1))
    (hK0 : K 0 = 0) (hK : ∀ j, K (j + 1) = K j * P j + Q j) (d : ℕ) :
    H 0 * ((List.range d).map P).prod - Z * K d = H d := by
  induction d with
  | zero => simp [hK0]
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.prod_append, hK, ← hstep d, ← ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    noncomm_ring
