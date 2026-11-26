import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common

/-- **The comparator block exposes one direction per state.** With bit-independent comparator
secrets `R_i`, every prefix row at cut `i` has comparator part `e_{κ(x)} ⊗ ρ_i` with the same
`ρ_i = r₀ R_1 ⋯ R_i`. Hence the comparator parts of all `2^i` prefix rows span at most `|S|`
dimensions (`|S| = 3`). After root-first projection (the projection lemma of
`pq-we-split-lemma-attempts` §7(iii)) the comparator rows of `A_i` are visible only through the
`|S|` vectors `ℓ^s_i = ρ_i A^s_i`; this is the scalar-row model of note `pq-we-two-pass-reroute`
(§2), in which the reroute reduces to one hidden row per chain level. -/
theorem AdvancedEncryption.WE.Reroute.comparator_span_finrank_le {K V S R : Type*} [Field K] [Fintype S] [Fintype R] [DecidableEq S]
    (κ : V → S) (ρ : R → K) :
    Module.finrank K (Submodule.span K (Set.range fun x : V =>
      fun sr : S × R => if sr.1 = κ x then ρ sr.2 else 0)) ≤ Fintype.card S := by sorry
