module

public import Definitions.Def_LatticeAttack_Attacks_Mitm_Sorted
import all Definitions.Def_LatticeAttack_Attacks_Guess_Collision

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Lattices.Mitm

open Guess SigabaNeo.SortedJoin

variable {q n m : ℕ} [Fact q.Prime]

/-- Candidate triples, retaining list multiplicities. -/
def triples (L R : List (Vec q n)) (E : List (Vec q m)) :=
  R.flatMap fun y ↦ E.flatMap fun z ↦ L.map fun x ↦ (x, y, z)

private theorem matrix_card :
    Fintype.card (PublicMatrix q m n) = q ^ (n * m) := by
  change Fintype.card (Fin m → Fin n → ZMod q) = _
  simp [← pow_mul]

private def isHit (s : Vec q n) (e : Vec q m) (A : PublicMatrix q m n)
    (t : Vec q n × Vec q n × Vec q m) :=
  decide (A.mulVec t.1 = A.mulVec s + e - A.mulVec t.2.1 - t.2.2)

private theorem single_bound (s x y : Vec q n) (e z : Vec q m) :
    (∑ A : PublicMatrix q m n, if isHit s e A (x, y, z) then 1 else 0) * q ^ m ≤
      q ^ (n * m) * (1 + (if x + y = s then 1 else 0) * q ^ m) := by
  classical
  by_cases h : x + y = s
  · have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (PublicMatrix q m n)))
        (fun A _ ↦ show (if isHit s e A (x, y, z) then 1 else 0) ≤ 1 by split <;> decide)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, matrix_card] at hb
    simp only [Finset.sum_boole] at hb
    simp [h, Nat.mul_add]
    exact (Nat.mul_le_mul_right _ hb).trans (Nat.le_add_left ..)
  · have hu := sub_ne_zero.mpr h
    have hn : 0 < n := by
      by_contra! hz
      obtain rfl : n = 0 := by omega
      exact h (Subsingleton.elim ..)
    have he (A : PublicMatrix q m n) :
        isHit s e A (x, y, z) = true ↔ A.mulVec (x + y - s) = e - z := by
      simp only [isHit, decide_eq_true_eq, Matrix.mulVec_sub, Matrix.mulVec_add]
      constructor <;> intro hh <;> linear_combination hh
    simp only [he, Finset.sum_boole, h, ite_false, zero_mul, add_zero, mul_one]
    simp only [Nat.cast_id]
    change (fibre (x + y - s) (e - z)).card * q ^ m ≤ _
    apply (Nat.mul_le_mul_right _ (fibre_card_le _ _ hu)).trans_eq
    rw [← pow_add, ← Nat.succ_mul, show (n - 1).succ = n by omega]

private theorem list_bound (ts : List (Vec q n × Vec q n × Vec q m)) (s : Vec q n)
    (e : Vec q m) :
    (∑ A : PublicMatrix q m n, (ts.filter (isHit s e A)).length) * q ^ m ≤
      q ^ (n * m) * (ts.length + (ts.filter fun t ↦ t.1 + t.2.1 = s).length * q ^ m) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨x, y, z⟩ := t
    have step := Nat.add_le_add (single_bound s x y e z) ih
    have cons_len {α : Type} (p : α → Bool) (a : α) (l : List α) :
        ((a :: l).filter p).length = (if p a then 1 else 0) + (l.filter p).length := by
      cases h : p a <;> simp [h, Nat.add_comm]
    simp only [cons_len, List.length_cons, Finset.sum_add_distrib, Nat.add_mul]
    by_cases h : x + y = s <;> simp [h, Nat.mul_add] at step ⊢ <;> omega

theorem expected_hits_le (L R : List (Vec q n)) (E : List (Vec q m)) (s : Vec q n)
    (e : Vec q m) :
    (∑ A : PublicMatrix q m n, (pairJoin (fun x ↦ code (A.mulVec x)) L
      (queries R E A (A.mulVec s + e))).1.length) * q ^ m ≤
      q ^ (n * m) * (L.length * R.length * E.length +
        ((triples L R E).filter fun t ↦ t.1 + t.2.1 = s).length * q ^ m) := by
  have he (A : PublicMatrix q m n) := (pairJoin_spec (fun x ↦ code (A.mulVec x)) L
    (queries R E A (A.mulVec s + e))).1.length_eq
  have hl : (triples L R E).length = L.length * R.length * E.length := by
    simp [triples, List.length_flatMap, mul_comm, mul_left_comm, mul_assoc]
  have hb := list_bound (triples L R E) s e
  rw [hl] at hb
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  rw [he]
  simp [triples, queries, List.flatMap_assoc, List.flatMap_map, List.filter_flatMap,
    List.filter_map, List.length_flatMap, Function.comp_def, isHit, code_inj]

theorem expected_comparisons_le (L R : List (Vec q n)) (E : List (Vec q m)) (s : Vec q n)
    (e : Vec q m) :
    (∑ A : PublicMatrix q m n, (sortedMitm L R E A (A.mulVec s + e)).2) * q ^ m ≤
      q ^ (n * m) * ((L.length * Nat.clog 2 (L.length + 1) +
        R.length * E.length * (Nat.clog 2 (L.length + 1) + 1)) * q ^ m +
        (L.length * R.length * E.length +
          ((triples L R E).filter fun t ↦ t.1 + t.2.1 = s).length * q ^ m)) := by
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun A _ ↦
    (sortedMitm_spec L R E A (A.mulVec s + e)).2)
  apply (Nat.mul_le_mul_right _ hc).trans
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, matrix_card, nsmul_eq_mul,
    Nat.add_mul]
  nlinarith only [expected_hits_le L R E s e]

end SigabaNeo.Lattices.Mitm

#print axioms SigabaNeo.Lattices.Mitm.expected_hits_le
#print axioms SigabaNeo.Lattices.Mitm.expected_comparisons_le
