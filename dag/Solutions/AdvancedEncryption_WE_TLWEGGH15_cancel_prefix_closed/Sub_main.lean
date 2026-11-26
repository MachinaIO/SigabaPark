import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

theorem solution {R : Type*} [Ring R] {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (J : Matrix ν ι R) (S : Fin h → Bool → Matrix ι ι R) (W : Fin h → Bool → Matrix ι κ R)
    (j : Fin h) (valid : (Fin h → Bool) → Prop)
    (hvalid : ∀ z, valid z →
      J * ((List.ofFn fun i => S i (z i)).take j).prod * W j (z j) = 0)
    (z z' : Fin h → Bool) (hz' : valid z') (hpre : ∀ i : Fin h, i ≤ j → z i = z' i) :
    J * ((List.ofFn fun i => S i (z i)).take j).prod * W j (z j) = 0 := by
  have htake : (List.ofFn fun i => S i (z i)).take j = (List.ofFn fun i => S i (z' i)).take j := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      have hn : n < j := by simp at h1; omega
      rw [hpre ⟨n, by omega⟩ (by simp [Fin.le_def]; omega)]
  rw [htake, hpre j le_rfl]
  exact hvalid z' hz'
