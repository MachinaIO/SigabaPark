import Definitions.Def_LatticeAttack_Reduction_Rogers_Coefficients

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev IntegerTuple (n k : ℕ) := Fin k → {v : Fin n → ℤ // v ≠ 0}

def tupleRank {n k : ℕ} (z : IntegerTuple n k) :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range fun i ↦ (z i).val))

theorem tupleRank_pos {n k} (hk : 0 < k) (z : IntegerTuple n k) : 0 < tupleRank z := by
  let i : Fin k := ⟨0, hk⟩
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  exact ⟨⟨(z i).val, Submodule.subset_span (Set.mem_range_self i)⟩,
    fun h ↦ (z i).property (congrArg Subtype.val h)⟩

theorem tupleRank_le {n k} (z : IntegerTuple n k) : tupleRank z ≤ k := by
  simpa [tupleRank, Set.finrank] using finrank_range_le_card (R := ℤ) (fun i ↦ (z i).val)

def tupleRankIndex {n k} (hk : 0 < k) (z : IntegerTuple n k) : Fin k :=
  ⟨tupleRank z - 1, by have := tupleRank_le z; omega⟩

theorem tupleRankIndex_succ {n k} (hk : 0 < k) (z : IntegerTuple n k) :
    (tupleRankIndex hk z).val + 1 = tupleRank z := by
  have := tupleRank_pos hk z
  simp only [tupleRankIndex]
  omega

def rankOrbitSum {n k} (hk : 0 < k) (D : Set (SL n)) (F : (Fin k → E n) → ℝ≥0∞)
    (r : Fin k) : ℝ≥0∞ :=
  ∑' z : (tupleRankIndex (n := n) hk) ⁻¹' {r},
    ∫⁻ g in D, F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z.val i).val j : ℝ))) ∂groupHaar n

def rankDiagramTerm {n k} (F : (Fin k → E n) → ℝ≥0∞) (r : Fin k) : ℝ≥0∞ :=
  ∑' q : ℕ, ∑' A : Diagram (r.val + 1) k (q + 1),
    congruenceCoefficient n k r q A * ∫⁻ v : Fin (r.val + 1) → E n,
      F (fun j ↦ ((q + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (A.entry i j : ℝ) • v i)
      ∂Measure.pi (fun _ ↦ volume)

theorem domain_split_by_rank {n k} (hk : 0 < k) (D : Set (SL n))
    (F : (Fin k → E n) → ℝ≥0∞) (hf : Measurable F) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      (groupHaar n D)⁻¹ * ∑ r, rankOrbitSum hk D F r := by
  rw [domainProbability, lintegral_smul_measure,
    lintegral_map (tupleWorkload_measurable hf) measurable_quotient_mk'',
    domain_lintegral_tupleWorkload _ _ hf]
  congr 1
  exact ((tsum_fintype _).symm.trans (tsum_fiberwise _ (tupleRankIndex hk))).symm

theorem rogers_of_rank_terms {n k} (hk : 0 < k) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin k → E n) → ℝ≥0∞) (hf : Measurable F)
    (h : ∀ r, rankOrbitSum hk D F r = groupHaar n D * rankDiagramTerm F r) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      diagramSum (congruenceCoefficient n) F := by
  let := groupHaar_rightInvariant n
  obtain ⟨_, _, _, hS⟩ := arithmetic_domain n
  have hμ : groupHaar n ≠ 0 := fun h ↦ hS (by rw [h]; rfl)
  simp_rw [domain_split_by_rank hk D F hf, h, ← Finset.mul_sum, ← mul_assoc,
    ENNReal.inv_mul_cancel (domain_mass_ne_zero _ hμ hd) hfin, one_mul]
  rfl

end SigabaNeo.Rogers
