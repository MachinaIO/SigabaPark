import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Matrix

/-- **Untwisted leaf criterion = degree-0 Nullstellensatz certificate.** If the constraint
secrets are bit-independent (every path carries the same product `v`), the path row of `z` is
`(j ⊙ 1_{U(z)}) ⊗ v`, where `U(z)` is the set of clauses that `z` falsifies. A separator then
exists iff some clause weights `λ` satisfy `∑_{k ∈ U(z)} λ_k = 1` for every assignment `z`, i.e.
`∑_k λ_k C_k ≡ 1` for the clause indicator polynomials `C_k` (a degree-0 Nullstellensatz
refutation, decidable by linear algebra). Inclusion–exclusion is the simplest obstruction
(note `pq-we-masked-overcomplete-leaf`). -/
theorem AdvancedEncryption.WE.MaskedLeaf.untwisted_separator_iff {K : Type*} [Field K] {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    [DecidableEq κ] (U : ι → Finset κ) (j : κ → K) (hj : ∀ k, j k ≠ 0) (v : ν → K)
    (hv : v ≠ 0) :
    (∃ ℓ : κ × ν → K, ∀ z,
        (fun p : κ × ν => (if p.1 ∈ U z then j p.1 else 0) * v p.2) ⬝ᵥ ℓ = 1) ↔
      ∃ lam : κ → K, ∀ z, ∑ k ∈ U z, lam k = 1 := by sorry
