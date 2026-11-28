import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution {I : Type} [Fintype I] [DecidableEq I] (w u v : I → ℝ)
    (keep : I → Bool) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (he : ∀ i, keep i = false → u i = v i) :
    |∑ i, w i*(u i-v i)| ≤ ∑ i, (if keep i then w i else 0) := by
  refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [abs_mul, abs_of_nonneg (hw i)]
  cases k : keep i with
  | false => simp [he i k]
  | true =>
    simp only [↓reduceIte]
    have b : |u i-v i| ≤ 1 := abs_le.mpr ⟨by linarith [(hu i).1,(hv i).2],
      by linarith [(hu i).2,(hv i).1]⟩
    simpa using mul_le_mul_of_nonneg_left b (hw i)
