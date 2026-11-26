import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Union

open Polynomial

theorem solution {K T : Type*} [Field K] [Fintype K] [DecidableEq K]
    (cert : Finset T) (res : T → Finset K[X]) (D h : ℕ)
    (hsize : ∀ t ∈ cert, (res t).card ≤ D)
    (hnz : ∀ t ∈ cert, ∀ p ∈ res t, p ≠ 0)
    (hdeg : ∀ t ∈ cert, ∀ p ∈ res t, p.natDegree ≤ h) :
    (Finset.univ.filter (fun a : K ↦ ∃ t ∈ cert, ∃ p ∈ res t, p.eval a = 0)).card ≤
      cert.card * D * h := by
  classical
  let bad := fun t ↦ (res t).biUnion fun p ↦ p.roots.toFinset
  have incl : Finset.univ.filter (fun a : K ↦ ∃ t ∈ cert, ∃ p ∈ res t, p.eval a = 0) ⊆
      cert.biUnion bad := by
    intro a ha
    obtain ⟨t, ht, p, hp, hz⟩ := (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_biUnion.mpr
      ⟨p, hp, Multiset.mem_toFinset.mpr ((mem_roots (hnz t ht p hp)).mpr hz)⟩⟩
  refine (Finset.card_le_card incl).trans (Finset.card_biUnion_le.trans ?_)
  calc
    _ ≤ ∑ _t ∈ cert, D * h := by
      refine Finset.sum_le_sum fun t ht ↦ Finset.card_biUnion_le.trans ?_
      calc
        _ ≤ ∑ _p ∈ res t, h := Finset.sum_le_sum fun p hp ↦
          (Multiset.toFinset_card_le _).trans ((card_roots' p).trans (hdeg t ht p hp))
        _ = (res t).card * h := by simp
        _ ≤ _ := Nat.mul_le_mul_right h (hsize t ht)
    _ = _ := by simp [Nat.mul_assoc]
