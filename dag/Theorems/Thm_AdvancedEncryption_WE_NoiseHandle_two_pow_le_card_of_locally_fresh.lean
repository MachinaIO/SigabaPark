import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith

theorem AdvancedEncryption.WE.NoiseHandle.two_pow_le_card_of_locally_fresh {ι X : Type*}
    (S : Finset ι) (P : Finset (ι → X)) (hne : P.Nonempty)
    (hfresh : ∀ g ∈ P, ∀ w ∈ S, ∃ g' ∈ P, g' w ≠ g w ∧ ∀ v, v ≠ w → g' v = g v) :
    2 ^ S.card ≤ P.card := by sorry
