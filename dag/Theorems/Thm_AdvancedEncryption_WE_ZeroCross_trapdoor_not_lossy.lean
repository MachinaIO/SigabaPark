import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **A level matrix with a trapdoor is never lossy.** If `A K = 1` (a right inverse `K`, the
exact form of a preimage trapdoor), then `s ↦ s A` is injective and every sample `s A + e`
decodes as `(s A + e) K = s + e K`. A reduction that samples GGH15 preimages under `A` cannot use
`A` in lossy mode; lossiness is available only for matrices it never inverts, where CVW18
Lemma 4.4 already crosses every zero entry (note `pq-we-zero-entry-crossing`, §3). -/
theorem AdvancedEncryption.WE.ZeroCross.trapdoor_not_lossy {R ι μ : Type*} [CommRing R] [Fintype ι] [Fintype μ] [DecidableEq ι]
    (A : Matrix ι μ R) (K : Matrix μ ι R) (hK : A * K = 1) :
    (∀ s s' : ι → R, s ᵥ* A = s' ᵥ* A → s = s') ∧
      ∀ (s : ι → R) (e : μ → R), (s ᵥ* A + e) ᵥ* K = s + e ᵥ* K := by sorry
