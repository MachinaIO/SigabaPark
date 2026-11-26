import Definitions.Def_WE_MaskedGGH15

open AdvancedEncryption.WE.MaskedGGH15

/-- **The departure zero is forced.** Let clause `j` be the equality clause `(x_a ∨ ¬x_b)`
between level `a` (an earlier copy) and level `b` (the last copy), `a ≠ b`. At level `b` the two
bits have complementary diagonal entries for `j` in CVW18's CNF branching program: exactly one of
`M_{b,c}` and `M_{b,¬c}` has a zero at `(j, j)`. So when the comparator's eq chain reads the bit
that keeps the clause alive, the departing bit kills it (an encoding of zero in the sibling class,
which may hold witnesses); leaf-first LWE on the clause block stops there. -/
theorem AdvancedEncryption.WE.LastPass.departure_kills_chain_clause {w h : ℕ} (Ψ : CNF w h)
    (a b : Fin h) (hab : a ≠ b) (j : Fin w)
    (hj : ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔ ((l = a ∧ c = true) ∨ (l = b ∧ c = false)))
    (c : Bool) : cnfMat Ψ b c j j + cnfMat Ψ b (!c) j j = 1 := by sorry
