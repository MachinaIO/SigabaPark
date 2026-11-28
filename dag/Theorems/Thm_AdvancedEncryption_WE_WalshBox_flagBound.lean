import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.flagBound {I : Type} [Fintype I] [DecidableEq I] (w u v : I → ℝ)
    (keep : I → Bool) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (he : ∀ i, keep i = false → u i = v i) :
    |∑ i, w i*(u i-v i)| ≤ ∑ i, (if keep i then w i else 0) := by sorry
