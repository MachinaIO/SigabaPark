import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

/-- **The encryptor's succinct-LWE trapdoor without a trapdoor for `B`.** Each column of `T` is the
flooding sample `y + [0; d_W(t − M y)]`, `y ← D_{Z^{ℓm+m}, σ}`, `M = [I_ℓ ⊗ B | W]`, `t` the
column of `I_ℓ ⊗ G`, where `d_W` is any short preimage map of `W` alone. If `Λ^⊥(M)` is smooth
at `σ`, this law is within `ℓ n k · (2θ + 6 M 4^{−M} + 3 · 2^M 4^{−M²})` of the assumption's
`trapdoorLaw`, with `M = ℓ m + m` and `θ = π M (b² + 2 σ M b) / σ²`. -/
theorem AdvancedEncryption.WE.LeafView.trapdoorLaw_flood_close (p : Params) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (dW : (Fin (p.ℓ * p.n) → ZMod p.q) → Fin p.m → ℤ)
    (hdW : ∀ v, W *ᵥ (fun j => ((dW v j : ℤ) : ZMod p.q)) = v) (b : ℕ)
    (hb : ∀ v j, |dW v j| ≤ b)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + b ≤ (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ))
    (hB : dualMassE (stacked B W) p.σ ≤ 1 / 2) :
    CloseTo
      ((sampleOptList ((List.finRange (p.ℓ * (p.n * p.k))).map fun c =>
          some (((sampleList (gaussZ (p.σ : ℝ) hσ) (p.ℓ * p.m + p.m)).map
              (fun l (j : Fin (p.ℓ * p.m + p.m)) => l.getD j default)).map fun y =>
            y + fun j : Fin (p.ℓ * p.m + p.m) =>
              if h : j.val < p.ℓ * p.m then (0 : ℤ) else
                dW ((fun i => blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i c) -
                  stacked B W *ᵥ fun j => ((y j : ℤ) : ZMod p.q))
                  ⟨j.val - p.ℓ * p.m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) j.isLt⟩))).map
        (Option.map fun cols r j => (cols.getD j.val 0) r))
      (trapdoorLaw p B W)
      ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          ((b : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) * b) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2)))) := by sorry
