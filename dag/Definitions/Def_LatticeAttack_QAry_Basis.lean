module

public import Definitions.Def_LatticeAttack_Planted_Probability
import all Definitions.Def_LatticeAttack_Planted_Probability
public import Definitions.Def_LatticeAttack_Reduction_LLL_Algorithm

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.QAry

open Planted (Coord)
open LLL.Algorithm (Rows)

variable {m n q : ℕ} [NeZero q]
variable (A : Matrix (Fin m) (Fin n) (ZMod q)) (c : Fin m → ZMod q)

abbrev col (j : Fin n) : Coord m n := .inr (.inl j)
abbrev last : Coord m n := .inr (.inr ())

def Member (z : Coord m n → ℤ) : Prop :=
  ∀ i, (z (.inl i) : ZMod q) + A i ⬝ᵥ (fun j ↦ (z (col j) : ZMod q)) =
    (z last : ZMod q) * c i

omit [NeZero q] in
theorem member_planted [Fact q.Prime] (e : Fin m → ℤ) (s : Fin n → ℤ) (z : Coord m n → ℤ) :
    Member A (fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i) z ↔
      Planted.member A e s z := Iff.rfl

/-- Rows in block form, with the first block scaled by the modulus. -/
def row : Coord m n → Coord m n → ℤ
  | .inl i, .inl k => if i = k then q else 0
  | .inr (.inl j), .inl k => -((A k j).val : ℤ)
  | .inr (.inr ()), .inl k => (c k).val
  | .inr (.inl j), .inr (.inl k) => if j = k then 1 else 0
  | .inr (.inr ()), .inr (.inr ()) => 1
  | _, _ => 0

theorem row_member (r : Coord m n) : Member A c (row A c r) := by
  intro i
  rcases r with k | j | ⟨⟩ <;>
    simp [row, dotProduct, apply_ite]

private theorem eval_left {R : Type*} [CommRing R] (g : Coord m n → R) (i : Fin m) :
    (∑ r, g r * (row A c r (.inl i) : R)) =
      g (.inl i) * q - (∑ j, g (col j) * (A i j).val) + g last * (c i).val := by
  simp [Fintype.sum_sum_type, row, col, last, apply_ite, sub_eq_add_neg, add_assoc]

private theorem eval_right {R : Type*} [CommRing R] (g : Coord m n → R) (t : Fin n ⊕ Unit) :
    (∑ r, g r * (row A c r (.inr t) : R)) = g (.inr t) := by
  rcases t with j | ⟨⟩ <;> simp [Fintype.sum_sum_type, row, apply_ite]

private theorem independent_cast (R : Type*) [CommRing R] [IsDomain R] [CharZero R] :
    LinearIndependent R (fun r k ↦ (row A c r k : R)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g h
  have hcoord (k : Coord m n) : ∑ r, g r * (row A c r k : R) = 0 := by
    simpa [Finset.sum_apply] using congrFun h k
  have hr (t) : g (.inr t) = 0 := (eval_right A c g t).symm.trans (hcoord _)
  intro r
  rcases r with i | t
  · have hi := hcoord (.inl i)
    rw [eval_left] at hi
    simpa [col, last, hr, NeZero.ne q] using hi
  · exact hr t

theorem row_independent : LinearIndependent ℤ (row A c) := by
  simpa using independent_cast A c ℤ

theorem row_real_independent : LinearIndependent ℝ (fun r k ↦ (row A c r k : ℝ)) :=
  independent_cast A c ℝ

theorem span_iff_member (z : Coord m n → ℤ) :
    z ∈ Submodule.span ℤ (Set.range (row A c)) ↔ Member A c z := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hl (g : Coord m n → ℤ) (i : Fin m) :
      (∑ r, g r • row A c r) (.inl i) =
        g (.inl i) * q - (∑ j, g (col j) * (A i j).val) + g last * (c i).val := by
    simpa [Finset.sum_apply] using eval_left A c g i
  have hr (g : Coord m n → ℤ) (t : Fin n ⊕ Unit) :
      (∑ r, g r • row A c r) (.inr t) = g (.inr t) := by
    simpa [Finset.sum_apply] using eval_right A c g t
  constructor
  · rintro ⟨g, rfl⟩ i
    simp only [hl, col, last, hr]
    simp [dotProduct, mul_comm]
  · intro h
    let b (i : Fin m) := z (.inl i) + (∑ j, z (col j) * (A i j).val) - z last * (c i).val
    have hd (i) : (q : ℤ) ∣ b i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [b, dotProduct, mul_comm, sub_eq_zero] using h i
    choose k hk using hd
    refine ⟨Sum.elim k (fun t ↦ z (.inr t)), ?_⟩
    funext r
    rcases r with i | t
    · rw [hl]
      simp only [Sum.elim_inl, col, last, Sum.elim_inr]
      rw [mul_comm (k i), ← hk]
      simp [b, col, last]
      ring
    · exact hr _ t

abbrev dim (m n : ℕ) := Fintype.card (Coord m n)

noncomputable abbrev indexEquiv := Fintype.equivFin (Coord m n)

noncomputable def rows : Rows (dim m n) (dim m n) :=
  fun r k ↦ row A c (indexEquiv.symm r) (indexEquiv.symm k)

def FinMember (z : Fin (dim m n) → ℤ) := Member A c (z ∘ indexEquiv)

theorem rows_member (r : Fin (dim m n)) : FinMember A c (rows A c r) := by
  simpa [FinMember, rows, Function.comp_def] using row_member A c (indexEquiv.symm r)

private theorem reindex_independent {R : Type*} [CommRing R] {v : Coord m n → Coord m n → R}
    (h : LinearIndependent R v) :
    LinearIndependent R (fun i j ↦ v (indexEquiv.symm i) (indexEquiv.symm j)) := by
  let E := LinearEquiv.funCongrLeft R R (indexEquiv (m := m) (n := n)).symm
  exact (h.comp _ indexEquiv.symm.injective).map' E.toLinearMap E.ker

theorem rows_independent : LinearIndependent ℤ (rows A c) :=
  reindex_independent (row_independent A c)

theorem rows_real_independent : LinearIndependent ℝ (fun r k ↦ (rows A c r k : ℝ)) :=
  reindex_independent (row_real_independent A c)

theorem rows_span_iff_member (z : Fin (dim m n) → ℤ) :
    z ∈ LLL.Algorithm.lattice (rows A c) ↔ FinMember A c z := by
  unfold FinMember LLL.Algorithm.lattice
  rw [← span_iff_member, Submodule.mem_span_range_iff_exists_fun,
    Submodule.mem_span_range_iff_exists_fun]
  let e := indexEquiv (m := m) (n := n)
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g ∘ e, ?_⟩
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply]
    rw [← e.sum_comp]
    simp [e, rows]
  · rintro ⟨g, hg⟩
    refine ⟨g ∘ e.symm, ?_⟩
    funext k
    have hk := congrFun hg (e.symm k)
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply] at hk ⊢
    rw [← e.sum_comp]
    simpa [e, rows] using hk

theorem exists_combination {z : Coord m n → ℤ} (hz : Member A c z) :
    ∃ g : Coord m n → ℤ, ∑ r, g r • row A c r = z :=
  (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((span_iff_member A c z).mpr hz)

theorem rows_exists_combination {z : Fin (dim m n) → ℤ} (hz : FinMember A c z) :
    ∃ g : Fin (dim m n) → ℤ, ∑ r, g r • rows A c r = z :=
  (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((rows_span_iff_member A c z).mpr hz)

#print axioms exists_combination
#print axioms rows_exists_combination
#print axioms member_planted
#print axioms row_member
#print axioms row_independent
#print axioms row_real_independent
#print axioms span_iff_member
#print axioms rows_member
#print axioms rows_independent
#print axioms rows_real_independent
#print axioms rows_span_iff_member

end SigabaNeo.QAry
