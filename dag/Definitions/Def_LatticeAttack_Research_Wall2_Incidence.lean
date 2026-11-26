module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.Wall2

open Finset

/-- In a finite ensemble with constant block size and constant point multiplicity,
the fraction hitting a prescribed set is at most its size times the point density.
Apply to nonzero residues and the nonzero parts of fixed-rank dual codes. -/
theorem incidenceTail {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (C : I → Finset V) (B : Finset V) (k t : ℕ)
    (size : ∀ i, (C i).card = k)
    (regular : ∀ v, (univ.filter fun i => v ∈ C i).card = t) :
    (univ.filter fun i => (B ∩ C i).Nonempty).card * Fintype.card V ≤
      B.card * Fintype.card I * k := by
  classical
  have count (S : Finset V) :
      ∑ i, (S ∩ C i).card = S.card * t := by
    simp_rw [Finset.card_eq_sum_ones, ← Finset.filter_mem_eq_inter,
      Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_filter]
    simp [regular]
  have total := count (univ : Finset V)
  simp [size] at total
  have hits : (univ.filter fun i => (B ∩ C i).Nonempty).card ≤ B.card * t := by
    rw [← count, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · exact Finset.card_pos.mpr h
    · exact Nat.zero_le _
  calc
    _ ≤ (B.card * t) * Fintype.card V := Nat.mul_le_mul_right _ hits
    _ = B.card * (Fintype.card V * t) := by ring
    _ = _ := by rw [← total]; ring

#print axioms incidenceTail

end SigabaNeo.Wall2
