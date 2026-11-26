import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

/-- **Flooding preimage sampling for any matrix** (generalizing `SigabaNeoStd`'s
`Trapdoor.Family.colLaw_close` from `Bmat` to any `M` with a short preimage map `d`): the law of
`y + d(u − M y)`, `y ← D_{Z^m,τ}`, is within `2θ + 6 m 4^{−m} + 3·2^m 4^{−m²}` of the coset
Gaussian `D_{Λ^⊥_u(M),τ}`, where `θ = π m (b² + 2 τ m b)/τ²`, when `|d(v)_j| ≤ b`, `τ ≥ 1`,
`τ √m + b ≤ τ m` and `Λ^⊥(M)` is smooth at `τ`. -/
theorem AdvancedEncryption.WE.LeafView.floodColumn_close {n m q : ℕ} [NeZero q] (τ : ℝ) (hτ : 0 < τ)
    (hτ1 : 1 ≤ τ) (M : Matrix (Fin n) (Fin m) (ZMod q)) (d : (Fin n → ZMod q) → Fin m → ℤ)
    (hd : ∀ v, M *ᵥ (fun j => ((d v j : ℤ) : ZMod q)) = v) (b : ℕ) (hb : ∀ v j, |d v j| ≤ b)
    (hrad : τ * Real.sqrt m + b ≤ τ * m) (u : Fin n → ZMod q) (hB : dualMassE M τ ≤ 1 / 2)
    {p : PMF (Fin m → ℤ)} (hp : cosetGauss M u τ hτ = some p) :
    CloseTo (((sampleList (gaussZ τ hτ) m).map (fun l (j : Fin m) => l.getD j default)).map
        fun y => y + d (u - M *ᵥ fun j => ((y j : ℤ) : ZMod q))) p
      (ENNReal.ofReal (2 * (Real.pi * m * ((b : ℝ) ^ 2 + 2 * (τ * m) * b) / τ ^ 2)) +
        (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) +
        ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2))) := by sorry
