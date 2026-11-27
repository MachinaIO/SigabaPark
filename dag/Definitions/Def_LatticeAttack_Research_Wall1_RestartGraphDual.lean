import Definitions.Def_LatticeAttack_Research_Wall1_MarkedLineage
import Definitions.Def_LatticeAttack_Research_Wall1_QaryMembership

set_option autoImplicit true

/-! The metric dual of the restart graph and its finite-field incidence law. -/

noncomputable section
namespace SigabaNeo.Wall1.DualExit
open QaryMembership Submodule Matrix
open scoped RealInnerProductSpace BigOperators

abbrev Coord (m n : ℕ) := Fin m ⊕ Fin n
abbrev Space (m n : ℕ) := EuclideanSpace ℝ (Coord m n)

variable {m n q : ℕ} [Fact q.Prime]

private theorem qpos : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos

/-- The raw graph has generators `q eᵢ` and `(Aⱼ,eⱼ)`, with least nonnegative lifts. -/
def rawGraph (A : Design m n q) : Submodule ℤ (Space m n) :=
  let b := EuclideanSpace.basisFun (Coord m n) ℝ
  markedGraphModule b q (fun j ↦ ∑ i, ((A i j).val : ℝ) • b (.inl i))

/-- Physical integer numerator. The sign converts the library's positive graph congruence
to the negative vertical component of the dual of the primal graph. -/
def numerator : Point m n ≃ (Coord m n → ℤ) where
  toFun z := Sum.elim z.1 (-z.2)
  invFun v := (fun i ↦ v (.inl i), fun j ↦ -v (.inr j))
  left_inv z := by ext i <;> simp
  right_inv z := by funext i; cases i <;> simp

def vector (q : ℕ) (z : Point m n) : Space m n :=
  WithLp.toLp 2 (fun i ↦ (numerator z i : ℝ) / q)

private def productSum (A : Design m n q) (u : Fin m → ℤ) (j : Fin n) : ℤ :=
  ∑ i, ((A i j).val : ℤ) * u i

private theorem congruences (A : Design m n q) (z : Point m n) :
    dual A z ↔ ∀ j, (q : ℤ) ∣ productSum A z.1 j - z.2 j := by
  change (reduce q z.1 ᵥ* A = reduce q z.2) ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
  simp [productSum, reduce, vecMul, dotProduct, mul_comm]

omit [Fact q.Prime] in
private theorem graph_tests (A : Design m n q) (x : Space m n) :
    x ∈ metricDual (rawGraph A) ↔
      (∀ i, ∃ u : ℤ, (u : ℝ) = q * x (.inl i)) ∧
      (∀ j, ∃ v : ℤ, (v : ℝ) = (∑ i, ((A i j).val : ℝ) * x (.inl i)) + x (.inr j)) := by
  let T := (1 : Submodule ℤ ℝ).comap (((innerₗ (Space m n)) x).restrictScalars ℤ)
  change rawGraph A ≤ T ↔ _
  rw [rawGraph, markedGraphModule, sup_le_iff, span_le, span_le]
  simp only [Set.range_subset_iff]
  have test (v : Space m n) : v ∈ (T : Set (Space m n)) ↔ ⟪x, v⟫ ∈ (1 : Submodule ℤ ℝ) := Iff.rfl
  simp only [test, ← Nat.cast_smul_eq_nsmul ℝ, inner_smul_right, inner_sum, inner_add_right,
    EuclideanSpace.inner_basisFun_real, mem_one]
  rfl

/-- Every metric-dual vector has a denominator-`q` integer numerator. -/
theorem exists_numerator (A : Design m n q) {x : Space m n} (hx : x ∈ metricDual (rawGraph A)) :
    ∃ z : Point m n, vector q z = x := by
  obtain ⟨h, v⟩ := (graph_tests A x).mp hx
  choose u hu using h
  choose k hk using v
  let z : Point m n := (u, fun j ↦ productSum A u j - (q : ℤ) * k j)
  refine ⟨z, ?_⟩
  ext (i | j)
  · change (u i : ℝ) / q = _
    rw [hu, mul_div_cancel_left₀ _ qpos.ne']
  · change ((-(productSum A u j - (q : ℤ) * k j) : ℤ) : ℝ) / q = _
    rw [div_eq_iff qpos.ne']
    simp only [Int.cast_neg, Int.cast_sub, Int.cast_mul, Int.cast_natCast, productSum,
      Int.cast_sum, hu, hk]
    simp_rw [← mul_left_comm (q : ℝ) ((A _ _).val : ℝ)]
    rw [← Finset.mul_sum]
    ring

/-- Exact equivalence between metric-dual membership and the column congruences. -/
theorem vector_mem_iff (A : Design m n q) (z : Point m n) :
    vector q z ∈ metricDual (rawGraph A) ↔ dual A z := by
  rw [graph_tests, congruences]
  have hq := (qpos (q := q)).ne'
  have vert (j : Fin n) : (∑ i, ((A i j).val : ℝ) * vector q z (.inl i)) +
      vector q z (.inr j) = ((productSum A z.1 j - z.2 j : ℤ) : ℝ) / q := by
    change (∑ i, ((A i j).val : ℝ) * ((z.1 i : ℝ) / q)) + ((-z.2 j : ℤ) : ℝ) / q = _
    simp only [productSum, Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_neg,
      ← mul_div_assoc, ← Finset.sum_div]
    ring
  simp only [vert]
  constructor
  · rintro ⟨_, hv⟩ j
    obtain ⟨k, hk⟩ := hv j
    refine ⟨k, ?_⟩
    exact_mod_cast (by linarith [(eq_div_iff hq).mp hk] :
      ((productSum A z.1 j - z.2 j : ℤ) : ℝ) = (q : ℝ) * k)
  · intro h
    refine ⟨fun i ↦ ⟨z.1 i, ?_⟩, fun j ↦ ?_⟩
    · change _ = q * ((z.1 i : ℝ) / q)
      field_simp
    · obtain ⟨k, hk⟩ := h j
      exact ⟨k, by simp [hk, hq]⟩

/-- Uniform probability as the fraction of designs satisfying the event. -/
def probability (P : Design m n q → Prop) : ℝ :=
  ((designs P).card : ℝ) / Fintype.card (Design m n q)

theorem probability_mono {P Q : Design m n q → Prop} (h : ∀ A, P A → Q A) :
    probability P ≤ probability Q := by
  classical
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.monotone_filter_right Finset.univ fun A _ ↦ h A))

/-- Each eligible numerator imposes exactly `n` uniform scalar constraints. -/
theorem vector_probability (z : Point m n) (hz : reduce q z.1 ≠ 0) :
    probability (fun A : Design m n q ↦ vector q z ∈ metricDual (rawGraph A)) = 1 / (q : ℝ)^n := by
  simp only [vector_mem_iff, probability]
  have h := dual_fixed z hz
  rw [Finset.card_univ] at h
  have ht : (0 : ℝ) < Fintype.card (Design m n q) := by exact_mod_cast Fintype.card_pos
  apply (div_eq_div_iff ht.ne' (pow_ne_zero _ qpos.ne')).mpr
  simpa using (show (((designs fun A : Design m n q ↦ dual A z).card : ℝ) * (q : ℝ)^n) =
    Fintype.card (Design m n q) by exact_mod_cast h)

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.exists_numerator
#print axioms SigabaNeo.Wall1.DualExit.vector_mem_iff
#print axioms SigabaNeo.Wall1.DualExit.vector_probability
