import Mathlib.Tactic.Common

/-- **Two-query saturation of decomposable label release (note `pq-we-hybrid-tool-combinations`, §2).** A garbled-circuit WE needs a static mechanism that releases input-wire labels `L i u b` (wire `i`, use `u`, value `b`) to the decryptor. If the label extracted from the public data `E w` for witness candidate `w` depends on `w` only through the bit `w i`, then two runs, on the all-false and the all-true candidate, give both labels of every wire at every use. With `nand_reach_saturate` this yields the output-1 label on every statement, so a one-label-per-bit mechanism cannot be decomposable. -/
theorem AdvancedEncryption.WE.Combine.two_query_label_release {n U : ℕ} {α β : Type*} (L : Fin n → Fin U → Bool → α)
    (E : (Fin n → Bool) → β) (g : Fin n → Fin U → β → α)
    (hrel : ∀ w i u, g i u (E w) = L i u (w i)) :
    ∀ i u b, ∃ w ∈ ({fun _ => false, fun _ => true} : Set (Fin n → Bool)),
      g i u (E w) = L i u b := by sorry
