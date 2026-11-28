import Mathlib

theorem AdvancedEncryption.WE.SuccinctPacket.trace_product {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (L : K →+ K) (σ : I → K →+* K) (trace : ∀ x, L x = ∑ i, σ i x)
    (binary : ∀ x, L x = 0 ∨ L x = 1) (m : J → Bool) (e : J → ℕ) (z t h v : K) :
    (∑ j, if m j then L (z*t^e j) * L (h*v^e j) else 0) =
    ∑ i, L ((z * σ i h) * (∑ j, if m j then (t * σ i v)^e j else 0)) := by sorry
