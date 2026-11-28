import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

theorem AdvancedEncryption.WE.AffineFiberScan.pivot_patch {n r k : Nat} (A : Matrix (Fin r) (Fin n) (ZMod 2))
    (B : Matrix (Fin k) (Fin n) (ZMod 2)) (p : Fin r → Fin n)
    (hA : ∀ i j, A i (p j) = if i = j then 1 else 0)
    (hB : ∀ i j, B i (p j) = 0) (x : Fin n → ZMod 2) (target : Fin r → ZMod 2) :
    let e := target - A.mulVec x
    let patched := x + fun s => ∑ j : Fin r, if p j = s then e j else 0
    A.mulVec patched = target ∧ B.mulVec patched = B.mulVec x := by sorry
