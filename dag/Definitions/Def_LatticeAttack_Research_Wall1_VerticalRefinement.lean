import Definitions.Def_LatticeAttack_Research_Wall1_VerticalWinnerIsometry
import Definitions.Def_LatticeAttack_Research_Wall1_MarkedIntegerSection
import Mathlib.Algebra.Module.ZLattice.Covolume

set_option autoImplicit true

/-! # The cyclic refinement for a positive-height shortest vector -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule WithLp ZLattice
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The class of the fractional horizontal part has exact order equal to the height.
Any smaller annihilator would give a strictly shorter positive multiple of the winner. -/
theorem verticalWinner_order (L : Submodule ℤ V) (u l : V) (hl : l ∈ L)
    (k : ℕ) (hk : 0 < k) (v : WindowSpace V)
    (hv : v = horizontalInclusion l + (k : ℝ) • toLp 2 (u, (1 : ℝ)))
    (hshort : ∀ w ∈ appendWindow L u, w ≠ 0 → ‖v‖ ≤ ‖w‖) :
    addOrderOf (L.mkQ ((k : ℝ)⁻¹ • l)) = k := by
  let x := (k : ℝ)⁻¹ • l
  let e := toLp 2 (u, (1 : ℝ))
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hv0 : v ≠ 0 := by
    have hs := congrArg WithLp.snd hv
    change v.snd = 0 + (k : ℝ) * 1 at hs
    rintro rfl
    change (0 : ℝ) = _ at hs
    linarith
  apply (addOrderOf_eq_iff hk).2
  constructor
  · rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hkR.ne']
    exact (Submodule.Quotient.mk_eq_zero L).2 hl
  · intro m hmk hm hz
    have hmx : m • x ∈ L := (Submodule.Quotient.mk_eq_zero L).1
      ((map_nsmul L.mkQ m x).trans hz)
    let c : ℝ := (m : ℝ) / k
    have hc : 0 < c := div_pos (by exact_mod_cast hm) hkR
    have hc1 : c < 1 := (div_lt_one hkR).2 (by exact_mod_cast hmk)
    have heq : c • v = horizontalInclusion (m • x) + m • e := by
      rw [hv, smul_add, smul_smul, show c * (k : ℝ) = m by
        dsimp [c]; field_simp, ← Nat.cast_smul_eq_nsmul ℝ m x,
        ← Nat.cast_smul_eq_nsmul ℝ m e, map_smul, show x = (k : ℝ)⁻¹ • l by rfl,
        map_smul, smul_smul]
      rfl
    have hmem : c • v ∈ appendWindow L u := by
      rw [heq]
      exact Submodule.add_mem_sup ⟨_, hmx, rfl⟩
        ((ℤ ∙ e).toAddSubmonoid.nsmul_mem (mem_span_singleton_self _) _)
    have hn := hshort _ hmem (smul_ne_zero hc.ne' hv0)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hn
    exact (not_lt_of_ge hn) (by nlinarith [mul_pos (sub_pos.mpr hc1) (norm_pos_iff.mpr hv0)])

/-- Adjoining one generator gives relative index equal to its order in the quotient. -/
theorem relIndex_adjoin_singleton {A : Type*} [AddCommGroup A] (L : Submodule ℤ A) (x : A) :
    L.toAddSubgroup.relIndex (L ⊔ ℤ ∙ x).toAddSubgroup = addOrderOf (L.mkQ x) := by
  let f := L.mkQ.toAddMonoidHom
  have hf : f.ker = L.toAddSubgroup := by
    ext y
    exact Submodule.Quotient.mk_eq_zero L
  have he : (ℤ ∙ x).toAddSubgroup = AddSubgroup.zmultiples x := by
    ext y
    exact mem_span_singleton.trans AddSubgroup.mem_zmultiples_iff.symm
  rw [show (L ⊔ ℤ ∙ x).toAddSubgroup = L.toAddSubgroup ⊔ (ℤ ∙ x).toAddSubgroup by
    ext y; simp only [Submodule.mem_toAddSubgroup, Submodule.mem_sup, AddSubgroup.mem_sup]]
  rw [AddSubgroup.relIndex_sup_left, ← hf, AddSubgroup.relIndex_ker, he,
    AddMonoidHom.map_zmultiples, Nat.card_zmultiples]
  rfl

theorem verticalWinner_index (L : Submodule ℤ V) (u l : V) (hl : l ∈ L)
    (k : ℕ) (hk : 0 < k) (v : WindowSpace V)
    (hv : v = horizontalInclusion l + (k : ℝ) • toLp 2 (u, (1 : ℝ)))
    (hshort : ∀ w ∈ appendWindow L u, w ≠ 0 → ‖v‖ ≤ ‖w‖) :
    L.toAddSubgroup.relIndex (L ⊔ ℤ ∙ ((k : ℝ)⁻¹ • l)).toAddSubgroup = k :=
  (relIndex_adjoin_singleton _ _).trans (verticalWinner_order L u l hl k hk v hv hshort)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.verticalWinner_order
#print axioms SigabaNeo.Wall1.relIndex_adjoin_singleton
#print axioms SigabaNeo.Wall1.verticalWinner_index
