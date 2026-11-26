import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

open Classical in
/-- **Tail bound for `Def_SuccinctLWE`'s `T`.** If `Λ^⊥([I_ℓ ⊗ B | W])` is smooth at `σ`, then
with probability at least `1 − ℓnk · 3 · 2^{−M'}` (`M' = ℓm + m`) no column of
`T ← trapdoorLaw p B W` has norm `≥ σ √M'` (an empty coset gives `T = none`, not counted here).
Hence every entry of `T` is below `E_T = σ √M'`, the public check of the leaf lemma. -/
theorem AdvancedEncryption.WE.LeafView.trapdoorLaw_tail (p : Params) (hσ : (0 : ℝ) < p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (hB : dualMassE (stacked B W) p.σ ≤ 1 / 2) :
    (trapdoorLaw p B W).toOuterMeasure {T | ∃ T', T = some T' ∧ ∃ c,
        (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) ≤
          ‖embed (p.ℓ * p.m + p.m) (fun a => T' a c)‖} ≤
      ((p.ℓ * (p.n * p.k) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (3 * (1 / 2) ^ (p.ℓ * p.m + p.m)) := by sorry
