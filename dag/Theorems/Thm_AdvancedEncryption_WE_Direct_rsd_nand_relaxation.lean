import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-- One-gate relaxation of the regular-syndrome-decoding encoding of NAND circuits (note
`pq-we-direct-algebraic-languages`). A NAND gate with input bits `a, b` and output bit `c` is
encoded by a block `u ∈ F_2^4` (columns indexed `00, 01, 10, 11`) with the `F_2`-linear constraints
`Σ u = 1`, `u₂ + u₃ = a`, `u₁ + u₃ = b`, `u₀ + u₁ + u₂ = c`. For ANY assignment of the gate
triples (consistent or not with NAND), blocks satisfying all these linear constraints exist and
their total Hamming weight is `G + 2 · #(violated gates)`: a valid gate costs weight `1`, a
violated one weight `3`. -/
theorem AdvancedEncryption.WE.Direct.rsd_nand_relaxation {G : ℕ} (a b c : Fin G → ZMod 2) :
    ∃ u : Fin G → Fin 4 → ZMod 2,
      (∀ g, u g 0 + u g 1 + u g 2 + u g 3 = 1 ∧ u g 2 + u g 3 = a g ∧ u g 1 + u g 3 = b g ∧
        u g 0 + u g 1 + u g 2 = c g) ∧
      (∑ g, (Finset.univ.filter (fun i => u g i ≠ 0)).card) =
        G + 2 * (Finset.univ.filter (fun g => c g ≠ 1 + a g * b g)).card := by sorry
