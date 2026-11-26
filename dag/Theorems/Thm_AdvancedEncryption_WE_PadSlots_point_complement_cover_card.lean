import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common

/-- **Pad-slot lower bound (note `pq-we-apg-width-ring-analysis`, §4).** A width-1 diagonal 0/1 pad slot pads a subcube. A walk that inserts one point per hop passes through a hybrid in which all strings but one are padded; at that hybrid at least `n` slots are live, whatever the order of the walk. -/
theorem AdvancedEncryption.WE.PadSlots.point_complement_cover_card {n : ℕ} {ι : Type*} [Fintype ι] (C : ι → Fin n → Option Bool)
    (p : Fin n → Bool)
    (hp : ∀ j, ¬ ∀ i, C j i = none ∨ C j i = some (p i))
    (hcov : ∀ x : Fin n → Bool, x ≠ p → ∃ j, ∀ i, C j i = none ∨ C j i = some (x i)) :
    n ≤ Fintype.card ι := by sorry
