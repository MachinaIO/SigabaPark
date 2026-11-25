import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.RingBoxes
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices Cslib
open scoped ENNReal

/-- **The abort probability of a leaf key**: with a trapdoor matrix whose rows have norm at most
`ρ`, `k N ρ ≤ τ`, the small box `famBall s` with `2^{Bb−1} − 1 − τ ≤ s` and the big box of `Bb`
bits, a try aborts with probability at most `2^{−κ}` when `m N (4τ + 1) 2^κ ≤ 2^{Bb}`. -/
theorem AdvancedEncryption.WE.Leaf.leafKey_abort_le {q N n m k : ℕ} [NeZero q]
    (M : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdecN : ∀ y c, cnorm (dec y c) ≤ 1) (ρ τ κ : ℕ) (hM : ∀ a, rnorm (rowOf M a) ≤ ρ)
    (hρ : k * N * ρ ≤ τ) (B : Matrix (Fin n) (Fin m) (Negacyclic (ZMod q) N))
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb) (hs : 2 ^ (Bb - 1) - 1 - τ ≤ s)
    (hτ : 4 * τ + 1 ≤ 2 ^ Bb) (hκ : m * N * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ Bb)
    (u : Fin n → Negacyclic (ZMod q) N) :
    boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y)) (fun z => M *ᵥ z) u none ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by sorry
