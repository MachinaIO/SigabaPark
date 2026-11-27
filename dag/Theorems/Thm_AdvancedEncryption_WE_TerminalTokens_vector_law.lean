import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.TerminalTokens.vector_law {I : Type} [Fintype I] [DecidableEq I]
    (side activeToken otherTruth : I → Bool) (test : (I → Bool × Bool) → ℝ) :
    (∑ h : I → Bool, test (fun i =>
      let other := otherTruth i ^^ h i
      (activeToken i ^^ other, if side i then other else activeToken i))) =
    ∑ p : I → Bool, test (fun i => (p i, activeToken i ^^ (side i && p i))) := by
  sorry
