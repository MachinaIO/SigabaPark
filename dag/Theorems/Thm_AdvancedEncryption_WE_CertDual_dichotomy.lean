import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

/-- Certificate-dual dichotomy (note `pq-we-new-directions`). For a noisy-linear ciphertext
`L u + e + β • t` (uniform `u`, noise `e`, message `β`, target `t`): if the target lies in the
range of `L` (a linear unsatisfiability certificate exists), the law of the ciphertext does not
depend on `β` (perfect hiding); otherwise some functional kills the range of `L` and sends `t` to
`1` (Fredholm alternative); and every functional that kills the range decrypts:
`h (L u + e + β • t) = h e + β * h t`. -/
theorem AdvancedEncryption.WE.CertDual.dichotomy {K U V : Type*} [Field K] [AddCommGroup U]
    [Module K U] [Fintype U] [AddCommGroup V] [Module K V] (L : U →ₗ[K] V) (t : V) :
    (t ∈ LinearMap.range L →
      ∀ (f : V → ℝ) (e : V) (β : K), ∑ u, f (L u + e + β • t) = ∑ u, f (L u + e)) ∧
    (t ∉ LinearMap.range L → ∃ h : Module.Dual K V, h.comp L = 0 ∧ h t = 1) ∧
    (∀ h : Module.Dual K V, h.comp L = 0 →
      ∀ (u : U) (e : V) (β : K), h (L u + e + β • t) = h e + β * h t) := by sorry
