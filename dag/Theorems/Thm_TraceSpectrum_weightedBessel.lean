import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem TraceSpectrum.weightedBessel {E I : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (s : Finset I) (v : I → E) (h : Orthonormal ℝ v)
    (a : I → ℝ) (ha : ∀ i ∈ s, |a i| ≤ ‖inner ℝ (v i) x‖) :
    ∑ i ∈ s, (a i)^2 ≤ ‖x‖^2 := by
  sorry
