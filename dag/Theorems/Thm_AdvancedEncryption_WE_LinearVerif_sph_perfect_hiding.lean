import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Card

open Matrix

/-- Perfect hiding of the linear hash-proof template on unsatisfiable checks. If the linear
check `M *ᵥ π = v` over a finite field has no solution, then for every value `a` of the
projected key `k ᵥ* M`, the hash `k ⬝ᵥ v` takes every value `t` on the same number of keys `k`:
given `k ᵥ* M`, the hash of a uniform key is uniform, so `(k ᵥ* M, k ⬝ᵥ v + μ)` hides `μ`
perfectly. (If a solution `π` exists, `k ⬝ᵥ v = (k ᵥ* M) ⬝ᵥ π` is determined instead.) Used
in the note `pq-we-proof-system-routes`. -/
theorem AdvancedEncryption.WE.LinearVerif.sph_perfect_hiding
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c]
    (M : Matrix r c K) (v : r → K) (h : ¬ ∃ π : c → K, M *ᵥ π = v) (a : c → K) (t t' : K) :
    (Finset.univ.filter (fun k : r → K => k ᵥ* M = a ∧ k ⬝ᵥ v = t)).card =
      (Finset.univ.filter (fun k : r → K => k ᵥ* M = a ∧ k ⬝ᵥ v = t')).card := by sorry
