import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem TraceSpectrum.conditionalGap {I : Type*} (s : Finset I) (w d c : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, |c i| = 1) :
    ∑ i ∈ s, |w i * d i * c i| = ∑ i ∈ s, w i * |d i| := by
  sorry
