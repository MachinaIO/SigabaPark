import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

open Classical in
/-- **The WE encryptor's own `(B, W, T)` is close to `Def_SuccinctLWE`'s.** The encryptor
(`encLaw`) draws `B` uniform with no trapdoor, `W = [A | H − A R]` with a gadget trapdoor
(`A` uniform, `R` uniform binary, `m = mb + ℓnk`) and each column of `T` by flooding with the short
preimage map of `W` (`floodT`). For a prime `q`, `σ ≥ 1`, `2σ ≤ q`, `3 m e^{−πσ²} ≤ 1/2` and
`σ √M' + ℓnk ≤ σ M'` (`M' = ℓm + m`), its law is within

    ℓnk (2θ + 6 M' 4^{−M'} + 3·2^{M'} 4^{−M'²})       (flooding, θ = π M' (b² + 2σM'b)/σ², b = ℓnk)
  + 4(ℓ+1)(12 m e^{−πσ²} + (q^n + q^{ℓn})(4/σ)^m)  (Λ^⊥([I_ℓ ⊗ B | W]) not smooth)
  + 2 · ℓnk √(q^{ℓn} / 2^{mb}) / 2                  (leftover hash lemma on A R, twice)

of the challenger's law (`chalLaw`: `B`, `W` uniform, `T ← trapdoorLaw p B W`). -/
theorem AdvancedEncryption.WE.LeafView.encryptorSetup_close (p : Params) [Fact p.q.Prime] (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hmb : 0 < mb) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ) (h2 : 2 * (p.σ : ℝ) ≤ p.q)
    (hexp : 3 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m ≤ 1 / 2)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + (p.ℓ * p.n * p.k : ℕ) ≤
      (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) :
    CloseTo (encLaw p mb hm hσ) (chalLaw p)
      ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          (((p.ℓ * p.n * p.k : ℕ) : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) *
            (p.ℓ * p.n * p.k : ℕ)) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2))) +
      ENNReal.ofReal (4 * (p.ℓ + 1) * (12 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m +
          ((p.q : ℝ) ^ p.n + (p.q : ℝ) ^ (p.ℓ * p.n)) * (4 / (p.σ : ℝ)) ^ p.m)) +
      2 * ENNReal.ofReal ((p.ℓ * p.n * p.k : ℕ) *
        (Real.sqrt ((p.q : ℝ) ^ (p.ℓ * p.n) * (2 ^ mb : ℝ)⁻¹) / 2))) := by sorry
