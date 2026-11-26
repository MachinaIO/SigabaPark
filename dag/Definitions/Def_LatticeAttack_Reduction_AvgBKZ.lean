module

public import Mathlib
public import Definitions.Def_LatticeAttack_Reduction_AvgBKZ_Gaussian
public import Definitions.Def_LatticeAttack_Reduction_AvgBKZ_Plane
public import Definitions.Def_LatticeAttack_Reduction_AvgBKZ_Selection

set_option autoImplicit true

/-! Coordinate projections of modular kernel lattices and the law of fresh quotient columns. -/

public section

namespace SigabaNeo.AvgBKZ

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

/-- Eliminate an integer prefix from a modular equation. The remaining constraint
is exactly its syndrome in the quotient by the prefix column space. -/
theorem coordinateProjection {X : Type*} (reduce : X → U) (h : Function.Surjective reduce)
    (A : U →ₗ[K] V) (b : V) :
    (∃ x, A (reduce x) + b = 0) ↔ A.range.mkQ b = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨-(reduce x), by rw [map_neg]; exact neg_eq_of_add_eq_zero_right hx⟩
  · rintro ⟨u, hu⟩
    obtain ⟨x, hx⟩ := h (-u)
    exact ⟨x, by simp [hx, hu]⟩

/-- Every fixed tuple of quotient columns has the same number of lifts, including
when the quotient is zero. Thus independent uniform columns stay independent uniform. -/
theorem quotientColumnCount (S : Submodule K V) (k : ℕ) (b : Fin k → V ⧸ S) :
    Nat.card {a : Fin k → V // ∀ i, S.mkQ (a i) = b i} = Nat.card S ^ k := by
  classical
  let split : {a : Fin k → V // ∀ i, S.mkQ (a i) = b i} ≃
      ((i : Fin k) → {v : V // S.mkQ v = b i}) :=
    { toFun := fun a i ↦ ⟨a.val i, a.property i⟩
      invFun := fun a ↦ ⟨fun i ↦ (a i).val, fun i ↦ (a i).property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let lift (i : Fin k) := (S.mkQ_surjective (b i)).choose
  have hl (i : Fin k) : S.mkQ (lift i) = b i := (S.mkQ_surjective (b i)).choose_spec
  let translate (i : Fin k) : {v : V // S.mkQ v = b i} ≃ S :=
    { toFun := fun v ↦ ⟨v.val - lift i, by
        have hz : S.mkQ (v.val - lift i) = 0 := by rw [map_sub, v.property, hl, sub_self]
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz⟩
      invFun := fun s ↦ ⟨s.val + lift i, by
        have hs : S.mkQ s.val = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact s.property
        rw [map_add, hs, zero_add, hl]⟩
      left_inv := fun _ ↦ Subtype.ext (sub_add_cancel _ _)
      right_inv := fun _ ↦ Subtype.ext (add_sub_cancel_right _ _) }
  rw [Nat.card_congr (split.trans (Equiv.piCongrRight translate)), Nat.card_fun, Nat.card_fin]

#print axioms coordinateProjection
#print axioms quotientColumnCount

end SigabaNeo.AvgBKZ
