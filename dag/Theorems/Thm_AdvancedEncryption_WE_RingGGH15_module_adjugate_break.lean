import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix in
/-- **Module adjugate break (note `pq-we-apg-width-ring-analysis`, §2).** Module-rank-`k` version of the ring kernel break: the explicit left kernel vector `(z0, -z1)` of `[S0; S1]` built from adjugates and determinants cancels the uniform `a`. Its entries are products of `2k - 1` secret entries, so the break works whenever `(sigma sqrt(dk))^{2k}` times the noise is below `q`; the module rank must grow like `log(q/sigma_E) / (2 log(sigma sqrt(dk)))`. -/
theorem AdvancedEncryption.WE.RingGGH15.module_adjugate_break {R : Type*} [CommRing R] {k : Type*} [Fintype k] [DecidableEq k]
    (S0 S1 : Matrix k k R) (u a e0 e1 : k → R) :
    (S1.det • (u ᵥ* S0.adjugate)) ⬝ᵥ (S0 *ᵥ a + e0)
      - (S0.det • (u ᵥ* S1.adjugate)) ⬝ᵥ (S1 *ᵥ a + e1)
      = (S1.det • (u ᵥ* S0.adjugate)) ⬝ᵥ e0 - (S0.det • (u ᵥ* S1.adjugate)) ⬝ᵥ e1 := by sorry
