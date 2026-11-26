import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-- Noise compounding in a Hamming-metric (LPN / code) GGH15 chain. A path evaluation `A_1 D_{1,w_1} ⋯ D_{L,w_L}` carries the noise `Σ_i S_{<i} E_i D_{>i}`; one output bit is `Σ_i r_iᵀ E_i h_i` with `r_i` a row of `S_{<i}` (nonzero) and `h_i` a column of `D_{>i}` (a sparse preimage, weight `≥ ρ`). For independent Bernoulli(`τ`) noise matrices `E_i` (flattened to one function on `Fin L × Fin m × Fin n`), its bias is exactly `(1 - 2τ)^{Σ_i wt(r_i) wt(h_i)}`, hence at most `(1 - 2τ)^{L ρ}`. With `ρ ≥ n / (2 log₂(2N + 2))` (`AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages`) and LPN security `τ n ≳ k ln 2`, this bounds the depth of any such chain; see the note `pq-we-non-lattice-ggh15-analogues`. -/
theorem AdvancedEncryption.WE.NonLattice.chain_noise_bias {L m n : ℕ} (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) (ρ : ℕ)
    (r : Fin L → Fin m → ZMod 2) (h : Fin L → Fin n → ZMod 2)
    (hr : ∀ i, r i ≠ 0) (hh : ∀ i, ρ ≤ (Finset.univ.filter fun b => h i b ≠ 0).card) :
    ∑ E : Fin L × Fin m × Fin n → ZMod 2,
        (∏ t, (if E t = 1 then τ else 1 - τ)) *
          (-1 : ℝ) ^ (∑ t, r t.1 t.2.1 * E t * h t.1 t.2.2).val
      = (1 - 2 * τ) ^ (∑ i, (Finset.univ.filter fun a => r i a ≠ 0).card *
          (Finset.univ.filter fun b => h i b ≠ 0).card) ∧
    (1 - 2 * τ) ^ (∑ i, (Finset.univ.filter fun a => r i a ≠ 0).card *
          (Finset.univ.filter fun b => h i b ≠ 0).card) ≤ (1 - 2 * τ) ^ (L * ρ) := by sorry
