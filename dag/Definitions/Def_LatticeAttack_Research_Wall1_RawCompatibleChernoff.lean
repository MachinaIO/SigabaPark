import Definitions.Def_LatticeAttack_Research_Wall1_RawCompatibleLine
import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleChernoff

set_option autoImplicit true

/-! A finite Gaussian partition bound for the actual compatible exceptional triples. -/
set_option maxRecDepth 4096
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane CenteredPrefixOccupancy QaryMembership OrderedFiberTuples
open AffineTripleChernoff
open scoped Classical

/-- Concatenate output and input coordinates. -/
def rawFullVector {k : ℕ} (z : Candidate k) : Fin (400+k) → ℤ :=
  Fin.append z.1 z.2

/-- Encode an ordered raw triple as three full vectors. -/
def rawTripleVector {k : ℕ} {T : Finset (Candidate k)} (e : orderedTuples T 3) :
    VectorTriple (400+k) :=
  (rawFullVector (e 0).val, rawFullVector (e 1).val, rawFullVector (e 2).val)

theorem rawTripleVector_injective {k : ℕ} {T : Finset (Candidate k)} :
    Function.Injective (rawTripleVector (T := T)) := by
  intro e f he
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  apply (Fin.appendEquiv (α := ℤ) 400 k).injective
  fin_cases i
  · exact congrArg Prod.fst he
  · exact congrArg (fun p : VectorTriple (400+k) ↦ p.2.1) he
  · exact congrArg (fun p : VectorTriple (400+k) ↦ p.2.2) he

/-- Fixed-parameter coordinate relation for the full raw vectors. -/
def rawTripleLine {k : ℕ} {T : Finset (Candidate k)} (t : ZMod 3329)
    (e : orderedTuples T 3) : Prop := ∀ i,
  ((rawTripleVector e).2.2 i : ZMod 3329) =
    (1-t) * ((rawTripleVector e).1 i : ZMod 3329) +
      t * ((rawTripleVector e).2.1 i : ZMod 3329)

lemma rawFullVector_centered_energy {k : ℕ} {R : ℝ} (z : Candidate k)
    (hz : z ∈ centeredBall k R) :
    (∀ i, -1664 ≤ rawFullVector z i ∧ rawFullVector z i ≤ 1664) ∧
      (∑ i, (rawFullVector z i : ℝ)^2) ≤ R^2 := by
  have hh := (mem_centeredBall R z).mp hz
  constructor
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [rawFullVector, Fin.append_left] using hh.1 j
    · simpa only [rawFullVector, Fin.append_right] using hh.2.1 j
  · simpa only [rawFullVector, Fin.sum_univ_add, Fin.append_left, Fin.append_right, sqLength]
      using hh.2.2

/-- Chernoff bound for any fixed-parameter subfamily of actual centered raw triples. -/
theorem raw_triple_fixed_parameter_bound {k : ℕ} (R β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (orderedTuples (centeredBall k R) 3)) (t : ZMod 3329)
    (hline : ∀ e ∈ S, rawTripleLine t e) :
    (S.card : ℝ) ≤ Real.exp (3 * β * R^2) * (scalarPartition t β)^(400+k) := by
  let U := S.image rawTripleVector
  have hc : U.card = S.card := card_image_of_injective _ rawTripleVector_injective
  rw [← hc]
  apply card_le_scalarPartition (400+k) U t R β hβ
  · intro p hp i
    obtain ⟨e, _, rfl⟩ := mem_image.mp hp
    exact ⟨(rawFullVector_centered_energy _ (e 0).property).1 i,
      (rawFullVector_centered_energy _ (e 1).property).1 i,
      (rawFullVector_centered_energy _ (e 2).property).1 i⟩
  · intro p hp
    obtain ⟨e, _, rfl⟩ := mem_image.mp hp
    exact ⟨(rawFullVector_centered_energy _ (e 0).property).2,
      (rawFullVector_centered_energy _ (e 1).property).2,
      (rawFullVector_centered_energy _ (e 2).property).2⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := mem_image.mp hp
    exact hline e he

/-- Every actual compatible triple belongs to a nontrivial fixed-parameter family. -/
theorem raw_compatible_exists_parameter {k : ℕ} (R : ℝ)
    (e : orderedTuples (centeredBall k R) 3)
    (he : e ∈ compatibleRankTwoTriples (centeredBall k R)) :
    ∃ t : ZMod 3329, (t ≠ 0 ∧ t ≠ 1) ∧ rawTripleLine t e := by
  obtain ⟨t, ht0, ht1, hi, ho⟩ := raw_compatible_triple_affine_line (centeredBall k R)
    (fun z hz ↦ ((mem_centeredBall R z).mp hz).2.1) e he
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · have hj := congrFun ho j
    simpa only [rawTripleVector, rawFullVector, Fin.append_left, rawAffinePoint,
      reduce, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hj
  · have hj := congrFun hi j
    simpa only [rawTripleVector, rawFullVector, Fin.append_right, rawAffinePoint,
      reduce, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hj

/-- Actual compatible rank-two triples are bounded by the sum of all nontrivial
scalar partition bounds, with no independence assumption on the candidates. -/
theorem raw_compatible_card_le_scalarPartitions (k : ℕ) (R β : ℝ) (hβ : 0 ≤ β) :
    ((compatibleRankTwoTriples (centeredBall k R)).card : ℝ) ≤
      Real.exp (3 * β * R^2) *
        ∑ t ∈ (univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1),
          (scalarPartition t β)^(400+k) := by
  let B := compatibleRankTwoTriples (centeredBall k R)
  let P := (univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1)
  let S (t : ZMod 3329) := B.filter (rawTripleLine t)
  have hcover : B ⊆ P.biUnion S := by
    intro e he
    obtain ⟨t, ht, hl⟩ := raw_compatible_exists_parameter R e he
    exact mem_biUnion.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht⟩, mem_filter.mpr ⟨he, hl⟩⟩
  have hc : B.card ≤ ∑ t ∈ P, (S t).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hreal : (B.card : ℝ) ≤ ∑ t ∈ P, ((S t).card : ℝ) := by exact_mod_cast hc
  calc
    (B.card : ℝ) ≤ ∑ t ∈ P, ((S t).card : ℝ) := hreal
    _ ≤ ∑ t ∈ P, Real.exp (3 * β * R^2) * (scalarPartition t β)^(400+k) := by
      apply sum_le_sum
      intro t ht
      exact raw_triple_fixed_parameter_bound R β hβ (S t) t
        (fun e he ↦ (mem_filter.mp he).2)
    _ = _ := by rw [mul_sum]

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_triple_fixed_parameter_bound
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_compatible_card_le_scalarPartitions
