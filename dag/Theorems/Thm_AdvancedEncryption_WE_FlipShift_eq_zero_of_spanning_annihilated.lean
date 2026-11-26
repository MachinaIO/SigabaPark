import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Shifts that vanish on every witness row vanish identically.** Over a field, if a family of
rows `c x` spans `K^κ` and every `c x ᵥ* M` is zero, then `M = 0`. Applied to the shift matrix
`M = W_k (T_W Z)` of `succinct_slot_shift`: statement-independence lets the witness prefix rows at
an overcomplete cut span the row space, so canonical decryption forces the hint's shift to be zero,
i.e. the hint must supply genuine `B`-preimages of the honest targets. -/
theorem AdvancedEncryption.WE.FlipShift.eq_zero_of_spanning_annihilated {K X κ μ : Type*} [Field K] [Fintype κ] [Fintype μ] [DecidableEq κ]
    (c : X → κ → K) (hspan : Submodule.span K (Set.range c) = ⊤)
    (M : Matrix κ μ K) (h : ∀ x, c x ᵥ* M = 0) : M = 0 := by sorry
