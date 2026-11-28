module

public import Definitions.Def_LatticeAttack_Research_Wall1_HeightZeroFloor
public import Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
public import Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta
import all Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta
import all Definitions.Def_LatticeAttack_Research_Wall1_HeightZeroFloor
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

open SampleDeletion CBDTail Matrix InnerProductSpace
open scoped BigOperators
open Classical

variable {N d : ℕ}

/-- Half-space tail for a displacement fixed by the symmetric projection. -/
theorem heightOneVector (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (h : EuclideanSpace ℝ (Fin N)) (fixed : Q.mulVec (WithLp.ofLp h) = WithLp.ofLp h) :
    (∑ w with ‖projectedCBD Q w + h‖ ^ 2 ≤ ‖projectedCBD Q w‖ ^ 2, jointWeight w) ≤
      Real.exp (-‖h‖ ^ 2 / 12) := by
  have inner_eq (w : Fin N → Digit 3) :
      ⟪projectedCBD Q w, h⟫_ℝ = projection (WithLp.ofLp h) w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    unfold projectedCBD
    rw [WithLp.ofLp_toLp]
    rw [← Matrix.dotProduct_transpose_mulVec, hs, fixed, dotProduct_comm]
    rfl
  have energy := EuclideanSpace.real_norm_sq_eq h
  have event (w : Fin N → Digit 3) :
      (‖projectedCBD Q w + h‖ ^ 2 ≤ ‖projectedCBD Q w‖ ^ 2) ↔
      projection (WithLp.ofLp h) w ≤ -((∑ i, h i ^ 2) / 2) := by
    rw [norm_add_sq_real, inner_eq]
    constructor <;> intro hw <;> linarith
  simp_rw [event]
  rw [energy]
  exact half_energy_tail _

/-- Height-one failure mass for the integer span of a basis in a fixed subspace. -/
theorem heightOneUnion (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (fixed : ∀ h : V, Q.mulVec (WithLp.ofLp h.val) = WithLp.ofLp h.val)
    (b : Module.Basis (Fin d) ℝ V) {g : ℝ} (hg : 0 < g)
    (floor : ∀ i, g ≤ ‖gramSchmidt ℝ b i‖) :
    (∑ w with ∃ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) ∧
      ‖projectedCBD Q w + h.val‖ ≤ ‖projectedCBD Q w‖, jointWeight w) ≤
      (∑' k : ℤ, Real.exp (-(g^2 / 12) * (k : ℝ)^2))^d - 1 := by
  classical
  let v (c : Fin d → ℤ) : V := ∑ i, (c i : ℝ) • b i
  let F (c : Fin d → ℤ) := Real.exp (-(1/12 : ℝ) * ‖v c‖^2)
  let A := Finset.univ.filter fun w ↦ ∃ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) ∧
    ‖projectedCBD Q w + h.val‖ ≤ ‖projectedCBD Q w‖
  have witness (w) (hw : w ∈ A) : ∃ c, c ≠ 0 ∧
      ‖projectedCBD Q w + (v c).val‖^2 ≤ ‖projectedCBD Q w‖^2 := by
    obtain ⟨h, hh, hn, hit⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hh
    have eq : v c = h := by simpa [v, Int.cast_smul_eq_zsmul] using hc
    refine ⟨c, fun hz ↦ hn ?_, ?_⟩
    · simp [← eq, hz, v]
    · rw [eq]
      exact pow_le_pow_left₀ (norm_nonneg _) hit 2
  let pick w := if hw : w ∈ A then (witness w hw).choose else 0
  have spec w (hw : w ∈ A) := (witness w hw).choose_spec
  let S := A.image pick
  have zero_out : 0 ∉ S := by
    intro hz
    obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hz
    exact (spec w hw).1 (by simpa [pick, hw] using eq)
  have mass : ∑ w ∈ A, jointWeight w ≤ ∑ c ∈ S, F c := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun w hw ↦ Finset.mem_image_of_mem pick hw)]
    apply Finset.sum_le_sum
    intro c _
    have bound := heightOneVector Q hs (v c).val (fixed _)
    apply le_trans _ (bound.trans_eq ?_)
    swap
    · unfold F
      congr 1
      change -‖v c‖^2 / 12 = -(1/12 : ℝ) * ‖v c‖^2
      ring
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ha, hc⟩ := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa [← hc, pick, ha] using (spec w ha).2
    · intros
      unfold jointWeight weight
      positivity
  have diag i : ⟪gramSchmidt ℝ b i, b i⟫_ℝ = ‖gramSchmidt ℝ b i‖^2 := by
    conv_lhs => rhs; rw [gramSchmidt_def'' ℝ b i]
    simp only [inner_add_right, real_inner_self_eq_norm_sq, inner_sum, real_inner_smul_right]
    rw [add_eq_left]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.mp hj).ne', mul_zero]
  have summ : Summable F := by
    simpa [F, v] using (affineTheta (s := (1/12 : ℝ)) (by norm_num) hg b
      (gramSchmidt ℝ b) floor diag (fun _ _ hij ↦ gramSchmidt_inv_triangular ℝ b hij) 0).1
  have partialSum := summ.sum_le_tsum (insert 0 S) (fun c _ ↦ (Real.exp_pos _).le)
  change (∑ c ∈ insert 0 S, F c) ≤ ∑' c, F c at partialSum
  rw [Finset.sum_insert zero_out, show F 0 = 1 by simp [F, v]] at partialSum
  have total := latticeTheta_le b (s := (1/12 : ℝ)) (by norm_num) hg floor
  change (∑' c, F c) ≤ _ at total
  change (∑ w ∈ A, jointWeight w) ≤ _
  rw [show g^2 / 12 = (1/12)*g^2 by ring]
  linarith

#print axioms heightOneVector
#print axioms heightOneUnion

end SigabaNeo.Wall1
