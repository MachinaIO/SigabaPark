import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **The succinct-LWE hint gives preimages under `B` only up to a `W`-shift.** Let
`[I_ℓ ⊗ B | W] T = I_ℓ ⊗ G` (`Def_SuccinctLWE`); its diagonal block `k` reads
`B T_k + W_k T_W = G`. Use `T_k Z` (with `Z = G⁻¹(Y)`) as a GGH15 preimage under the level matrix
`B` of a target `Y = G Z`. A level value `s B + e` continued through it gives `s Y + e T_k Z` minus
the **shift** `(s W_k)(T_W Z)`, a uniform-looking row (`W_k` uniform) times a short matrix. Canonical
decryption needs the shift to cancel, which needs the `W`-part `s W_k` (then
`stacked_hint_decodes` applies) or targets with known short `B`-preimages (preimage-first). -/
theorem AdvancedEncryption.WE.FlipShift.succinct_slot_shift {R : Type*} [CommRing R] {n m m' g p : Type*} [Fintype n] [Fintype m]
    [Fintype m'] [Fintype g]
    (B : Matrix n m R) (Wk : Matrix n m' R) (Tk : Matrix m g R) (TW : Matrix m' g R)
    (G : Matrix n g R) (h : B * Tk + Wk * TW = G) (Z : Matrix g p R) (s : n → R) (e : m → R) :
    (s ᵥ* B + e) ᵥ* (Tk * Z) = s ᵥ* (G * Z) - (s ᵥ* Wk) ᵥ* (TW * Z) + e ᵥ* (Tk * Z) := by sorry
