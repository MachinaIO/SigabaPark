import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **The succinct-LWE hint is a decoding trapdoor for stacked samples.** With the block
identities `B T_{k'k} + W_{k'} T_{W,k} = δ_{k'k} G` of `[I_ℓ ⊗ B | W] T = I_ℓ ⊗ G`, the slot samples
`s_{k'} B + e_{k'}` together with the `W`-part `∑ s_{k'} W_{k'} + e_W` map under `T` to
`s_k G` plus the short noise `∑ e_{k'} T_{k'k} + e_W T_{W,k}`, from which `s_k` and the noise are
read off. So a GGH15 level of succinct shape whose values expose the `W`-part (needed to cancel the
shift of `succinct_slot_shift`) is decodable by whoever holds `T`, and the decoded-defect barrier
applies to every reduction that uses `T`. -/
theorem AdvancedEncryption.WE.FlipShift.stacked_hint_decodes {R : Type*} [CommRing R] {ι n m m' g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [Fintype m] [Fintype m'] [Fintype g]
    (B : Matrix n m R) (W : ι → Matrix n m' R) (T : ι → ι → Matrix m g R)
    (TW : ι → Matrix m' g R) (G : Matrix n g R)
    (h : ∀ k' k, B * T k' k + W k' * TW k = if k' = k then G else 0)
    (s : ι → n → R) (e : ι → m → R) (eW : m' → R) (k : ι) :
    (∑ k', (s k' ᵥ* B + e k') ᵥ* T k' k) + (∑ k', s k' ᵥ* W k' + eW) ᵥ* TW k =
      s k ᵥ* G + ((∑ k', e k' ᵥ* T k' k) + eW ᵥ* TW k) := by sorry
