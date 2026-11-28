import Definitions.Def_LatticeAttack_Research_Wall1_RawThirdMomentExact
import Definitions.Def_LatticeAttack_Research_Wall1_CenteredInputReduction
import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleLine

set_option autoImplicit true

/-! Compatible raw rank-two triples obey a common nontrivial affine relation. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane QaryMembership AffineGraphMoments OrderedFiberTuples
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Distinct centered input blocks remain distinct after reduction modulo3329. -/
theorem raw_triple_reduced_inputs_injective {k : ℕ} (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (e : orderedTuples T 3) (he : e ∈ distinctInputTriples T) :
    Function.Injective (fun i ↦ (rawAffinePoint (e i).val).2) := by
  intro a b hab
  apply (mem_filter.mp he).2
  exact centered_reduce_injective _ _ (hT _ (e a).property) (hT _ (e b).property) hab

/-- Each compatible exceptional triple has a common affine parameter for both
input and output blocks, and that parameter is neither zero nor one. -/
theorem raw_compatible_triple_affine_line {k : ℕ} (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (e : orderedTuples T 3) (he : e ∈ compatibleRankTwoTriples T) :
    ∃ t : ZMod 3329, t ≠ 0 ∧ t ≠ 1 ∧
      (rawAffinePoint (e 2).val).2 =
        (1-t) • (rawAffinePoint (e 0).val).2 + t • (rawAffinePoint (e 1).val).2 ∧
      (rawAffinePoint (e 2).val).1 =
        (1-t) • (rawAffinePoint (e 0).val).1 + t • (rawAffinePoint (e 1).val).1 := by
  have hc := (mem_filter.mp he).2
  have hr := (mem_filter.mp (mem_filter.mp he).1).2
  have hd := (mem_filter.mp (mem_filter.mp he).1).1
  have hi := raw_triple_reduced_inputs_injective T hT e hd
  obtain ⟨t, ht⟩ := inputRows_rank_two_affine_line
    (fun i ↦ rawAffinePoint (e i).val) (raw_triple_inputs_ne T hT e hd) hr
  refine ⟨t, ?_, ?_, ht, compatible_outputs_affine_line _ t ht hc⟩
  · intro hzero
    subst t
    simp only [sub_zero, one_smul, zero_smul, add_zero] at ht
    have heq := hi ht
    exact (by decide : (2 : Fin 3) ≠ 0) heq
  · intro hone
    subst t
    simp only [sub_self, zero_smul, one_smul, zero_add] at ht
    have heq := hi ht
    exact (by decide : (2 : Fin 3) ≠ 1) heq

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_triple_reduced_inputs_injective
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_compatible_triple_affine_line
