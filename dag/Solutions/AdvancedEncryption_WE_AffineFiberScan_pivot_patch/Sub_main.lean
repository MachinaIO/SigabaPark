import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

theorem solution {n r k : Nat} (A : Matrix (Fin r) (Fin n) (ZMod 2))
    (B : Matrix (Fin k) (Fin n) (ZMod 2)) (p : Fin r → Fin n)
    (hA : ∀ i j, A i (p j) = if i = j then 1 else 0)
    (hB : ∀ i j, B i (p j) = 0) (x : Fin n → ZMod 2) (target : Fin r → ZMod 2) :
    let e := target - A.mulVec x
    let patched := x + fun s => ∑ j : Fin r, if p j = s then e j else 0
    A.mulVec patched = target ∧ B.mulVec patched = B.mulVec x := by
  let e := target - A.mulVec x
  let correction := fun s => ∑ j : Fin r, if p j = s then e j else 0
  have dot {m : Nat} (F : Matrix (Fin m) (Fin n) (ZMod 2)) (i : Fin m) :
      F.mulVec correction i = ∑ j, F i (p j) * e j := by
    simp only [Matrix.mulVec, dotProduct, correction, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_ite]
  change A.mulVec (x+correction) = target ∧ B.mulVec (x+correction) = B.mulVec x
  simp only [Matrix.mulVec_add]
  constructor
  · funext i
    simp [dot, hA, ite_mul, e]
  · funext i
    simp [dot, hB]
