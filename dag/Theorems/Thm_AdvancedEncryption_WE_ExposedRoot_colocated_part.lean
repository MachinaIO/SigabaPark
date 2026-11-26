import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

/-- **Co-location (note `pq-we-exposed-root-reachable-lemma`, §3).** A reachable row at level
`L-1` is `Σ_q β_q · P Ŝ_q` over prefixes `q` of length `L-1`. The column block of a prefix-cube
pad slot is `S_q` if `q = π` (its prefix) and `0` otherwise (shared pad secrets, unit start
weights). For two slots with the same prefix `π`, the parts of every reachable row in their
columns are therefore `β_π X_c` and `β_π X_d` with the *same* coefficient `β_π`; with shared
secrets `X_c = X_d = S_π`, so every reachable row lies in the span of the sum direction
`g = a^{(d)} + a^{(c)}`, and the difference direction `h = a^{(c)}` has a short lift. -/
theorem AdvancedEncryption.WE.ExposedRoot.colocated_part {R : Type*} [Ring R] {Q a n k : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype n]
    (β : Q → Matrix a n R) (π : Q) (Xc Xd : Matrix n k R) :
    (∑ q, β q * (if q = π then Xc else 0)) = β π * Xc ∧
    (∑ q, β q * (if q = π then Xd else 0)) = β π * Xd := by sorry
