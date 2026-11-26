import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Common

/-- **Decryption recovers the integer noise (note `pq-we-two-sided-lwe`, §4 item 2).** If
`b = ℓ + z (mod q)` entrywise with `2|z| < q`, then the centred lift of `b − ℓ` is `z`. A
decryptor who knows the label `ℓ` (from a witness) learns the exact noise, which is the
"textbook attack" that LWE with trapdoor hints (ePrint 2026/2927) must avoid by `σ_e σ_t ≳ q m`;
correct GGH15 decryption always lies in that attack regime. -/
theorem AdvancedEncryption.WE.TwoSided.decryption_recovers_noise {μ : Type*} (q : ℕ) [NeZero q] (b ℓ : μ → ZMod q) (z : μ → ℤ)
    (hb : ∀ j, b j = ℓ j + (z j : ZMod q)) (hz : ∀ j, 2 * |z j| < q) :
    ∀ j, (b j - ℓ j).valMinAbs = z j := by sorry
