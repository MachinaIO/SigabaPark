import Definitions.Def_LatticeAttack_Research_Wall1_RankinWindow

set_option autoImplicit true

/-! # Restricting the vertical Rankin infimum to primitive horizontal sublattices -/

noncomputable section
namespace SigabaNeo.Wall1

open Module Submodule WithLp
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {L : Submodule ℤ V} {n : ℕ}

/-- The tuple generates the entire intersection of its real span with the old lattice. -/
def RankinFamily.IsPrimitive (b : RankinFamily L n) : Prop :=
  span ℤ (Set.range b.vec) = L ⊓ (span ℝ (Set.range b.vec)).restrictScalars ℤ

omit [FiniteDimensional ℝ V] in
/-- Saturation preserves the real plane and can only decrease its intrinsic covolume. -/
theorem RankinFamily.exists_primitive [DiscreteTopology L] (b : RankinFamily L n) :
    ∃ c : RankinFamily L n, c.IsPrimitive ∧ span ℝ (Set.range c.vec) = span ℝ (Set.range b.vec) ∧
      familyVolume c.vec ≤ familyVolume b.vec := by
  let K := span ℝ (Set.range b.vec)
  let H := L.comap (K.subtype.restrictScalars ℤ)
  let d : Basis (Fin n) ℝ K := Basis.span b.ind
  let D := span ℤ (Set.range d)
  have hd (j) : (d j : V) = b.vec j := Basis.coe_span_apply b.ind j
  have hDH : D ≤ H := span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    change (d j : V) ∈ L
    rw [hd]; exact b.mem j)
  have : DiscreteTopology H := DiscreteTopology.of_continuous_injective
    (f := fun x : H ↦ (⟨x.val.val, x.property⟩ : L))
    (by fun_prop) (fun x y h ↦ Subtype.ext (Subtype.ext (congrArg (fun a : L ↦ a.val) h)))
  have : IsZLattice ℝ H := ⟨by
    apply top_unique
    calc ⊤ = span ℝ (D : Set K) := IsZLattice.span_top.symm
         _ ≤ _ := span_mono (fun _ hx ↦ hDH hx)⟩
  have hr : finrank ℤ H = n := by rw [ZLattice.rank ℝ H, Module.finrank_eq_card_basis d,
    Fintype.card_fin]
  let z := Module.finBasisOfFinrankEq ℤ H hr
  let e := z.ofZLatticeBasis ℝ H
  have heSpan : span ℤ (Set.range e) = H := z.ofZLatticeBasis_span ℝ
  let c : RankinFamily L n := ⟨K.subtype ∘ ⇑e, fun j ↦ by
    change (e j) ∈ H
    rw [show e j = (z j : K) from z.ofZLatticeBasis_apply ℝ H j]
    exact (z j).property, e.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr K.injective_subtype)⟩
  have hK : span ℝ (Set.range c.vec) = K := by
    change span ℝ (Set.range (K.subtype ∘ ⇑e)) = _
    rw [Set.range_comp, ← map_span, e.span_eq, Submodule.map_top, K.range_subtype]
  have hprim : c.IsPrimitive := by
    rw [RankinFamily.IsPrimitive, hK]
    change span ℤ (Set.range ((K.subtype.restrictScalars ℤ) ∘ ⇑e)) = _
    rw [Set.range_comp, ← map_span, heSpan, Submodule.map_comap_eq, inf_comm]
    congr 1
    ext x
    exact ⟨fun ⟨y, he⟩ ↦ he ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  refine ⟨c, hprim, hK, ?_⟩
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have hvol (t : Basis (Fin n) ℝ K) :
      familyVolume (K.subtype ∘ ⇑t) = ENNReal.ofReal (ZLattice.covolume (span ℤ (Set.range t))) := by
    unfold familyVolume
    rw [show Matrix.gram ℝ (K.subtype ∘ ⇑t) = Matrix.gram ℝ t by rfl,
      ← covolume_span_sq_eq_gram t]
    exact congrArg ENNReal.ofReal (Real.sqrt_sq ENNReal.toReal_nonneg)
  have hidx := ZLattice.covolume_div_covolume_eq_relIndex' D H hDH
  have hpos : (0 : ℝ) < D.toAddSubgroup.relIndex H.toAddSubgroup :=
    hidx ▸ div_pos (ZLattice.covolume_pos D) (ZLattice.covolume_pos H)
  have hnat : 0 < D.toAddSubgroup.relIndex H.toAddSubgroup := by exact_mod_cast hpos
  have hone : (1 : ℝ) ≤ D.toAddSubgroup.relIndex H.toAddSubgroup := by exact_mod_cast hnat
  change familyVolume (K.subtype ∘ ⇑e) ≤ _
  rw [← show K.subtype ∘ ⇑d = b.vec from funext hd, hvol, hvol, heSpan]
  apply ENNReal.ofReal_le_ofReal
  simpa using (le_div_iff₀ (ZLattice.covolume_pos H)).mp (hone.trans_eq hidx.symm)

private theorem verticalMinimum_span_congr (u : V) {b c : Fin n → V}
    (h : span ℝ (Set.range b) = span ℝ (Set.range c)) : verticalMinimum L u b = verticalMinimum L u c := by
  have hh : span ℝ (Set.range (horizontalInclusion ∘ b)) =
      span ℝ (Set.range (horizontalInclusion ∘ c)) := by
    simp only [Set.range_comp, ← map_span, h]
  apply iInf_congr
  intro w
  change ENNReal.ofReal ‖(span ℝ (Set.range (horizontalInclusion ∘ b)))ᗮ.starProjection _‖ = _
  congr 2
  exact congrArg (fun K : Submodule ℝ (WindowSpace V) ↦ Kᗮ.starProjection w.val.val) hh

/-- The exact vertical infimum can be taken over primitive rank-n sublattices alone. -/
theorem rankin_append_primitive [DiscreteTopology L] (u : V) (n : ℕ) :
    rankinMinimum (appendWindow L u) (n + 1) =
      min (rankinMinimum L (n + 1)) (⨅ c : {b : RankinFamily L n // b.IsPrimitive},
        familyVolume c.val.vec * verticalMinimum L u c.val.vec) := by
  rw [rankin_append]
  congr 1
  apply le_antisymm
  · exact le_iInf fun c ↦ iInf_le _ c.val
  · apply le_iInf
    intro b
    obtain ⟨c, hp, hs, hle⟩ := b.exists_primitive
    refine (iInf_le (fun c : {b : RankinFamily L n // b.IsPrimitive} ↦
      familyVolume c.val.vec * verticalMinimum L u c.val.vec) ⟨c, hp⟩).trans ?_
    rw [show verticalMinimum L u c.vec = verticalMinimum L u b.vec from verticalMinimum_span_congr u hs]
    exact mul_le_mul_left hle _

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.RankinFamily.exists_primitive
#print axioms SigabaNeo.Wall1.rankin_append_primitive
