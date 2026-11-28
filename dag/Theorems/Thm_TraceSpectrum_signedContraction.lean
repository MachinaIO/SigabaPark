import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem TraceSpectrum.signedContraction {I : Type*} (s : Finset I) (w v : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, |v i| ≤ 1)
    (total : ∑ i ∈ s, w i = 1) :
    |∑ i ∈ s, w i * v i| ≤ 1 := by
  sorry
