import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Common

theorem solution {X ρ : Type*} [Fintype X] [DecidableEq X] [Fintype ρ] (W : ρ → ℕ)
    (f : (r : ρ) → X → Fin (W r)) (F : Finset ((r : ρ) × Fin (W r))) (k : ℕ)
    (hsmall : ∀ p ∈ F, (Finset.univ.filter fun x => f p.1 x = p.2).card ≤ k)
    (hcover : ∀ x, ∃ p ∈ F, f p.1 x = p.2) :
    Fintype.card X ≤ k * ∑ r, W r := by
  classical
  have hsub : (Finset.univ : Finset X) ⊆
      F.biUnion fun p => Finset.univ.filter fun x => f p.1 x = p.2 := by
    intro x _
    obtain ⟨p, hp, hx⟩ := hcover x
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
  calc Fintype.card X = (Finset.univ : Finset X).card := Finset.card_univ.symm
    _ ≤ (F.biUnion fun p => Finset.univ.filter fun x => f p.1 x = p.2).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ F, (Finset.univ.filter fun x => f p.1 x = p.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ F, k := Finset.sum_le_sum hsmall
    _ = F.card * k := by simp
    _ ≤ Fintype.card ((r : ρ) × Fin (W r)) * k :=
        Nat.mul_le_mul_right _ (Finset.card_le_univ F)
    _ = k * ∑ r, W r := by simp [Fintype.card_sigma, mul_comm]
