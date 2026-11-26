import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

open Classical in
/-- **`Λ^⊥([I_ℓ ⊗ B | W])` is smooth for most uniform `(B, W)`.** For a prime `q`, `τ ≥ 1`,
`2τ ≤ q` and `3 m e^{−πτ²} ≤ 1/2`, the number of pairs `(B, W) ∈ Z_q^{n×m} × Z_q^{ℓn×m}` whose
`[I_ℓ ⊗ B | W]` has nonzero dual mass above `1/2` at width `τ` (the smoothness hypothesis of
`trapdoorLaw_flood_close` and of `cosetGauss_tail`) is at most a
`4(ℓ+1) (12 m e^{−πτ²} + (q^n + q^{ℓn}) (4/τ)^m)` fraction of all pairs. -/
theorem AdvancedEncryption.WE.LeafView.card_bad_stacked {n m q ℓ : ℕ} [Fact q.Prime] {τ : ℝ}
    (hτ : 1 ≤ τ) (h2 : 2 * τ ≤ q) (hm : 3 * Real.exp (-(Real.pi * τ ^ 2)) * m ≤ 1 / 2) :
    ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞) ≤
      (q : ℝ≥0∞) ^ (n * m) * (q : ℝ≥0∞) ^ (ℓ * n * m) *
        ENNReal.ofReal (4 * (ℓ + 1) * (12 * Real.exp (-(Real.pi * τ ^ 2)) * m +
          ((q : ℝ) ^ n + (q : ℝ) ^ (ℓ * n)) * (4 / τ) ^ m)) := by sorry
