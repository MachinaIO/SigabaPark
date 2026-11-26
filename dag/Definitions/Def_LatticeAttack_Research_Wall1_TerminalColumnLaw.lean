import Definitions.Def_LatticeAttack_Research_Wall1_TerminalGridFrame

set_option autoImplicit true

/-! # Raw columns and ordered signed minimizers for the graph tour -/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Module Submodule WithLp DecoupledDecoder
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V]
variable {m q : ℕ} (L : Submodule ℤ V) (g : Fin m → V)
local notation "K" => markedPreimage L g

def columnLift (c : Fin m → ZMod q) : V := ∑ i, (c i).val • g i

theorem columnLift_mem (c : Fin m → ZMod q) : columnLift g c ∈ K := by
  rw [markedPreimage_eq]
  apply mem_sup_right
  exact sum_mem fun i _ ↦ (span ℤ (Set.range g)).toAddSubmonoid.nsmul_mem
    (subset_span (Set.mem_range_self i)) _

theorem torsion_preimage (hg : ∀ i, q • g i ∈ L) {x : V} (hx : x ∈ K) : q • x ∈ L := by
  rw [markedPreimage_eq] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp hb
  rw [nsmul_add, Finset.smul_sum]
  exact L.add_mem (L.toAddSubmonoid.nsmul_mem ha _) (sum_mem fun i _ ↦
    (smul_comm q (c i) (g i)) ▸ L.smul_mem _ (hg i))

private def coordHom (hg : ∀ i, q • g i ∈ L) (i : Fin m) : ZMod q →+ V ⧸ L :=
  ZMod.lift q ⟨zmultiplesHom _ (L.mkQ (g i)), by
    change (q : ℤ) • L.mkQ (g i) = 0
    rw [natCast_zsmul, ← map_nsmul]
    exact (Quotient.mk_eq_zero L).2 (hg i)⟩

private theorem coordHom_cast (hg : ∀ i, q • g i ∈ L) (i : Fin m) (k : ℤ) :
    coordHom L g hg i (k : ZMod q) = k • L.mkQ (g i) := ZMod.lift_coe _ _ _

private def residue (hg : ∀ i, q • g i ∈ L) : (Fin m → ZMod q) →+ V ⧸ L where
  toFun c := ∑ i, coordHom L g hg i (c i)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

private theorem residue_eq [NeZero q] (hg : ∀ i, q • g i ∈ L) (c : Fin m → ZMod q) :
    residue L g hg c = L.mkQ (columnLift g c) := by
  change (∑ i, coordHom L g hg i (c i)) = _
  rw [columnLift, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := coordHom_cast L g hg i ((c i).val : ℤ)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, natCast_zsmul, map_nsmul] using h

def columnMark [NeZero q] (hg : ∀ i, q • g i ∈ L) : (Fin m → ZMod q) →+ Marks L K :=
  (residue L g hg).codRestrict _ fun c ↦
    ⟨_, columnLift_mem L g c, (residue_eq L g hg c).symm⟩

theorem columnMark_repr [NeZero q] (hg : ∀ i, q • g i ∈ L) (c : Fin m → ZMod q) :
    L.mkQ (columnLift g c) = (columnMark L g hg c).val := (residue_eq L g hg c).symm

theorem columnMark_surjective [NeZero q] (hg : ∀ i, q • g i ∈ L) :
    Function.Surjective (columnMark L g hg) := by
  intro z
  obtain ⟨x, hx, he⟩ := z.property
  rw [markedPreimage_eq] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp hb
  refine ⟨fun i ↦ (c i : ZMod q), Subtype.ext ?_⟩
  change (∑ i, coordHom L g hg i (c i : ZMod q)) = _
  rw [← he, map_add, (show L.mkQ a = 0 from (Quotient.mk_eq_zero L).2 ha), zero_add, map_sum]
  simp [coordHom_cast]

variable [InnerProductSpace ℝ V]

theorem modulus_witness (u : V) (hu : q • u ∈ L) (hq : q ≠ 0) :
    ∃ z ∈ appendWindow L u, z ≠ 0 ∧ ‖z‖ ≤ (q : ℝ) := by
  let z : WindowSpace V := toLp 2 (0, q)
  refine ⟨z, (mem_append_at_height L u z (q : ℤ) (by simp [z])).2 ?_, ?_, ?_⟩
  · change L.mkQ 0 = _
    rw [natCast_zsmul, ← map_nsmul, map_zero, (show L.mkQ (q • u) = 0 from (Quotient.mk_eq_zero L).2 hu)]
  · intro he
    have h := congrArg WithLp.snd he
    exact hq (by exact_mod_cast (show (q : ℝ) = 0 from h))
  · simp [z, WithLp.norm_toLp_snd]

variable [FiniteDimensional ℝ V]

/-- The least signed shortest vector for any fixed linear order on ambient keys. -/
theorem exists_orderedShortest {α : Type*} [LinearOrder α] (key : V → α)
    [DiscreteTopology L] (hn : L ≠ ⊥) :
    ∃ v, IsShortest L v ∧ ∀ w, IsShortest L w → key v ≤ key w := by
  obtain ⟨v, hv, hv0, he⟩ := ZLattice.exists_norm_eq_minimum hn
  have hs : IsShortest L v :=
    ⟨hv, hv0, fun w hw hw0 ↦ he ▸ ZLattice.minimum_le_norm hw hw0⟩
  have hfin : (Metric.closedBall (0 : V) ‖v‖ ∩ (L : Set V)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
      L.toAddSubgroup.isClosed_of_discreteTopology
  have hsub : {w | IsShortest L w} ⊆ Metric.closedBall (0 : V) ‖v‖ ∩ (L : Set V) :=
    fun w hw ↦ ⟨mem_closedBall_zero_iff.mpr (hw.2.2 v hv hv0), hw.1⟩
  exact Set.exists_min_image _ key (hfin.subset hsub) ⟨v, hs⟩

end SigabaNeo.Wall1.TerminalProjection
#print axioms SigabaNeo.Wall1.TerminalProjection.columnMark_surjective
#print axioms SigabaNeo.Wall1.TerminalProjection.modulus_witness
#print axioms SigabaNeo.Wall1.TerminalProjection.exists_orderedShortest
