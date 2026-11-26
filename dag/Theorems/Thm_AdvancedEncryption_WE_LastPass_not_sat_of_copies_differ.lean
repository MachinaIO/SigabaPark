import Definitions.Def_WE_MaskedGGH15

open AdvancedEncryption.WE.MaskedGGH15

/-- **Orphans are not zeros.** If `Ψ` contains both equality clauses `(x_a ∨ ¬x_b)` and
`(¬x_a ∨ x_b)` between the levels `a` and `b` (two copies of one witness bit), then every string
with `z_a ≠ z_b` falsifies one of them, so it does not satisfy `Ψ`. Hence the hypothesis of the
equality-cube flip reduces to the consistent strings. -/
theorem AdvancedEncryption.WE.LastPass.not_sat_of_copies_differ {w h : ℕ} (Ψ : CNF w h)
    (a b : Fin h)
    (h1 : ∃ j : Fin w, ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔
      ((l = a ∧ c = true) ∨ (l = b ∧ c = false)))
    (h2 : ∃ j : Fin w, ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔
      ((l = a ∧ c = false) ∨ (l = b ∧ c = true)))
    (z : Fin h → Bool) (hz : z a ≠ z b) : ¬ Sat Ψ z := by sorry
