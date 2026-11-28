import Definitions.Def_LatticeAttack_Research_Wall1_RawThirdMomentExact
import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleLine
import Definitions.Def_LatticeAttack_Research_Wall1_FiniteAffineLineCount

set_option autoImplicit true

/-! A fiber bound for the actual exceptional rank-two triple count. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane QaryMembership AffineGraphMoments OrderedFiberTuples
open FiniteAffineLineCount
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Centered integer inputs and a reduced-input fiber bound control rank-two triples. -/
theorem rankTwoTriples_card_le {k : ℕ} (T : Finset (Candidate k))
    (hin : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (B : ℝ)
    (hB : ∀ y : Fin k → ZMod 3329,
      ((T.filter fun z ↦ reduce 3329 z.2 = y).card : ℝ) ≤ B) :
    ((rankTwoTriples T).card : ℝ) ≤ (T.card : ℝ)^2 * 3329 * B := by
  let f : Candidate k → (Fin k → ZMod 3329) := fun z ↦ reduce 3329 z.2
  let g : Candidate k → Candidate k → ZMod 3329 → (Fin k → ZMod 3329) :=
    fun a b t ↦ (1-t) • f a + t • f b
  let S := ((T ×ˢ T) ×ˢ T).filter fun p ↦ ∃ t, f p.2 = g p.1.1 p.1.2 t
  have hc : (rankTwoTriples T).card ≤ S.card := by
    apply card_le_card_of_injOn (fun e : orderedTuples T 3 ↦
      (((e 0).val, (e 1).val), (e 2).val))
    · intro e he
      have hd := (mem_filter.mp he).1
      have hr := (mem_filter.mp he).2
      have hl := inputRows_rank_two_affine_line (fun i ↦ rawAffinePoint (e i).val)
        (raw_triple_inputs_ne T hin e hd) hr
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨(e 0).property, (e 1).property⟩,
        (e 2).property⟩, ?_⟩
      exact hl
    · intro a ha b hb h
      apply Function.Embedding.ext
      intro i
      apply Subtype.ext
      fin_cases i
      · exact congrArg (fun p ↦ p.1.1) h
      · exact congrArg (fun p ↦ p.1.2) h
      · exact congrArg Prod.snd h
  have hb := parametrized_triples_card_le_real T f g B (by
    intro y
    apply le_of_eq_of_le _ (hB y)
    apply congrArg (fun U : Finset (Candidate k) ↦ (U.card : ℝ))
    ext z
    simp only [mem_filter, f])
  have hcr : ((rankTwoTriples T).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hc
  simp only [ZMod.card, Nat.cast_ofNat] at hb
  apply hcr.trans
  apply le_of_eq_of_le _ hb
  apply congrArg (fun U : Finset ((Candidate k × Candidate k) × Candidate k) ↦ (U.card : ℝ))
  ext p
  simp only [S, mem_filter]

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rankTwoTriples_card_le
