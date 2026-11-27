import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open scoped BigOperators

theorem AdvancedEncryption.WE.TerminalTokens.pooled_cutoff (T need : ℕ) :
    ((Finset.univ : Finset (Fin T)).powerset.filter (fun x => x.card < need)).card =
      ∑ i ∈ Finset.range need, T.choose i := by
  sorry
