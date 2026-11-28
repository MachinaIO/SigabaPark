module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionCBD
import all Definitions.Def_LatticeAttack_Planted_Probability
import all Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionCBD

set_option autoImplicit true

public section
namespace SigabaNeo.Wall1.Decoupled

open SigabaNeo.Planted SigabaNeo.SampleDeletion

variable {m n q : ℕ}
abbrev Point (m n : ℕ) := Coord m n → ℤ
abbrev heightIndex : Coord m n := .inr (.inr ())
abbrev Design (m n q : ℕ) := Matrix (Fin m) (Fin n) (ZMod q)

private def row (A : Design m n q) (i : Fin m) : Point m n →+ ZMod q where
  toFun z := (z (.inl i) : ZMod q) + A i ⬝ᵥ (fun j ↦ (z (col j) : ZMod q))
  map_zero' := by simp [dotProduct]
  map_add' x y := by simp [dotProduct, mul_add, Finset.sum_add_distrib]; abel

/-- The integer horizontal lattice is determined by the design alone. -/
def L0 (A : Design m n q) : AddSubgroup (Point m n) where
  carrier := {z | z heightIndex = 0 ∧ ∀ i, row A i z = 0}
  zero_mem' := ⟨rfl, fun _ ↦ map_zero _⟩
  add_mem' := fun hx hy ↦ ⟨by simp [hx.1, hy.1], fun i ↦ by simp [hx.2 i, hy.2 i]⟩
  neg_mem' := fun hx ↦ ⟨by simp [hx.1], fun i ↦ by simp [hx.2 i]⟩

variable [Fact q.Prime] (A : Design m n q) (e : Fin m → ℤ) (s : Fin n → ℤ)

private theorem member_row (z : Point m n) :
    member A e s z ↔ ∀ i, row A i z = z heightIndex • row A i (plantedPoint e s) := by
  simp [member, last, heightIndex, row, col, plantedPoint, zsmul_eq_mul, mul_add, add_comm]

theorem sub_height_mem {z : Point m n} (hz : member A e s z) :
    z - z heightIndex • plantedPoint e s ∈ L0 A := by
  refine ⟨by simp [heightIndex, plantedPoint], fun i ↦ ?_⟩
  rw [map_sub, map_zsmul, (member_row A e s z).mp hz i, sub_self]

theorem add_plant_mem {w : Point m n} (hw : w ∈ L0 A) (k : ℤ) :
    member A e s (w + k • plantedPoint e s) := by
  apply (member_row A e s _).mpr
  intro i
  have h := hw.1
  rw [map_add, map_zsmul, hw.2 i, zero_add]
  simp [h, heightIndex, plantedPoint]

/-- Internal direct sum, expressed as existence and uniqueness of both coordinates. -/
theorem member_iff_unique_split (z : Point m n) :
    member A e s z ↔ ∃! p : L0 A × ℤ, z = p.1.val + p.2 • plantedPoint e s := by
  constructor
  · intro hz
    refine ⟨(⟨_, sub_height_mem A e s hz⟩, z heightIndex), (sub_add_cancel ..).symm, ?_⟩
    rintro ⟨w,k⟩ he
    change z = w.val + k • plantedPoint e s at he
    have hw := w.property.1
    have hk := congrFun he heightIndex
    change w.val heightIndex = 0 at hw
    simp [hw, heightIndex, plantedPoint] at hk
    apply Prod.ext
    · apply Subtype.ext
      change w.val = z - z heightIndex • plantedPoint e s
      rw [show z heightIndex = k from hk]
      exact eq_sub_of_add_eq he.symm
    · exact hk.symm
  · rintro ⟨⟨w,k⟩, rfl, _⟩
    exact add_plant_mem A e s w.property k

theorem horizontal_member_set :
    {z : Point m n | member A e s z ∧ z heightIndex = 0} = (L0 A : Set (Point m n)) := by
  ext z
  change (member A e s z ∧ z heightIndex = 0) ↔ z heightIndex = 0 ∧ ∀ i, row A i z = 0
  rw [member_row]
  by_cases h : z heightIndex = 0 <;> simp [h]

theorem reducer_constant {α : Type*} (F : Set (Point m n) → α) :
    F {z | member A e s z ∧ z heightIndex = 0} = F (L0 A) :=
  congrArg F (horizontal_member_set A e s)

section
open Classical in
/-- On a design fiber, an event may use the common output P to test the CBD plant. -/
theorem fiber_count {α : Type*} [DecidableEq α] {η : ℕ}
    (F : Design m n q → α) (P : α) (E : α → (Fin m → ℤ) → (Fin n → ℤ) → Prop) :
    (∑ B, integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
      if F B = P ∧ E (F B) (retained x) (secret x) then 1 else 0)) =
    (Finset.univ.filter fun B ↦ F B = P).card *
      integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
        if E P (retained x) (secret x) then 1 else 0) := by
  classical
  rw [← Nat.nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : F B = P <;> simp [h, integrate_const]

open Classical in
theorem joint_count {α : Type*} {η : ℕ}
    (F : Design m n q → α) (P : α) (S : Set ((Fin m → ℤ) × (Fin n → ℤ))) :
    (∑ B, integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
      if F B = P ∧ (retained x, secret x) ∈ S then 1 else 0)) =
    (Finset.univ.filter fun B ↦ F B = P).card *
      integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
        if (retained x, secret x) ∈ S then 1 else 0) :=
  fiber_count (η := η) F P (fun _ e' s' ↦ (e', s') ∈ S)

open Classical in
theorem projected_count {η : ℕ}
    (F : Design m n q → Matrix (Coord m n) (Coord m n) ℝ) (P : Matrix (Coord m n) (Coord m n) ℝ)
    (S : Set (Coord m n → ℝ)) :
    (∑ B, integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
      if F B = P ∧ (F B).mulVec (fun i ↦ (plantedPoint (retained x) (secret x) i : ℝ)) ∈ S
      then 1 else 0)) =
    (Finset.univ.filter fun B ↦ F B = P).card *
      integrate (m+n) (fun x : Fin (m+n) → Digit η ↦
        if P.mulVec (fun i ↦ (plantedPoint (retained x) (secret x) i : ℝ)) ∈ S then 1 else 0) :=
  fiber_count (η := η) F P (fun Q e' s' ↦ Q.mulVec (fun i ↦ (plantedPoint e' s' i : ℝ)) ∈ S)

end
#print axioms sub_height_mem
#print axioms add_plant_mem
#print axioms member_iff_unique_split
#print axioms horizontal_member_set
#print axioms reducer_constant
#print axioms fiber_count
#print axioms joint_count
#print axioms projected_count
end SigabaNeo.Wall1.Decoupled
