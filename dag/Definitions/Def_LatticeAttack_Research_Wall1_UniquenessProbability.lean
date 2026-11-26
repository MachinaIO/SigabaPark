module

public import Definitions.Def_LatticeAttack_Research_Wall1_HeightOne
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDQuadratic
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

open CBDQuadratic

theorem highHit (h y : EuclideanSpace ℝ (Fin N)) (k : ℝ) (hk : 2 ≤ k)
    (hit : ‖h + k • y‖^2 + k^2 ≤ ‖y‖^2 + 1) :
    h ≠ 0 ∧ ⟪y,h⟫_ℝ ≤ -(‖h‖^2/(2*k)) := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ k)] at hit
  have extra := mul_nonneg (show 0 ≤ k^2-1 by nlinarith [sq_nonneg (k-2)]) (sq_nonneg ‖y‖)
  constructor
  · rintro rfl
    simp at hit
    nlinarith [sq_nonneg (k-2)]
  · rw [real_inner_comm, ← neg_div, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (k-2)]

theorem highVector (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (h : EuclideanSpace ℝ (Fin N)) (fixed : Q.mulVec (WithLp.ofLp h) = WithLp.ofLp h)
    (k : ℝ) (hk : 2 ≤ k) :
    (∑ w with ‖h + k • projectedCBD Q w‖ ^ 2 + k^2 ≤ ‖projectedCBD Q w‖ ^ 2 + 1, jointWeight w) ≤
      Real.exp (-‖h‖ ^ 2 / (12*k^2)) := by
  have inner_eq (w : Fin N → Digit 3) :
      ⟪projectedCBD Q w, h⟫_ℝ = projection (WithLp.ofLp h) w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    unfold projectedCBD
    rw [WithLp.ofLp_toLp]
    rw [← Matrix.dotProduct_transpose_mulVec, hs, fixed, dotProduct_comm]
    rfl
  have hkpos : 0 < k := by linarith
  apply le_trans _ (lower_tail (WithLp.ofLp h) (‖h‖^2/(2*k)) (by positivity)) |>.trans_eq
  swap
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by intros; unfold jointWeight weight; positivity)
    intro w hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← inner_eq]
    exact (highHit _ _ k hk (Finset.mem_filter.mp hw).2).2
  · congr 1
    rw [← EuclideanSpace.real_norm_sq_eq h]
    by_cases hz : ‖h‖ = 0
    · simp [hz]
    · field_simp
      ring

set_option maxHeartbeats 1600000 in
theorem highUnion (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (fixed : ∀ h : V, Q.mulVec (WithLp.ofLp h.val) = WithLp.ofLp h.val)
    (b : Module.Basis (Fin d) ℝ V) {g : ℝ} (hg : 0 < g)
    (floor : ∀ i, g ≤ ‖gramSchmidt ℝ b i‖)
    (k : ℝ) (hk : 2 ≤ k) :
    (∑ w with ∃ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) ∧
      ‖h.val + k • projectedCBD Q w‖^2 + k^2 ≤ ‖projectedCBD Q w‖^2 + 1, jointWeight w) ≤
      (∑' m : ℤ, Real.exp (-(g^2 / (12*k^2)) * (m : ℝ)^2))^d - 1 := by
  classical
  have hkpos : 0 < k := by linarith
  let v (c : Fin d → ℤ) : V := ∑ i, (c i : ℝ) • b i
  let F (c : Fin d → ℤ) := Real.exp (-(1/(12*k^2) : ℝ) * ‖v c‖^2)
  let A := Finset.univ.filter fun w ↦ ∃ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) ∧
    ‖h.val + k • projectedCBD Q w‖^2 + k^2 ≤ ‖projectedCBD Q w‖^2 + 1
  have witness (w) (hw : w ∈ A) : ∃ c, c ≠ 0 ∧
      ‖(v c).val + k • projectedCBD Q w‖^2 + k^2 ≤ ‖projectedCBD Q w‖^2 + 1 := by
    obtain ⟨h, hh, hn, hit⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hh
    have eq : v c = h := by simpa [v, Int.cast_smul_eq_zsmul] using hc
    refine ⟨c, fun hz ↦ hn ?_, ?_⟩
    · simp [← eq, hz, v]
    · rw [eq]
      exact hit
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
    have bound := highVector Q hs (v c).val (fixed _) k hk
    apply le_trans _ (bound.trans_eq ?_)
    swap
    · unfold F
      congr 1
      change -‖v c‖^2 / (12*k^2) = -(1/(12*k^2) : ℝ) * ‖v c‖^2
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
    simpa only [F, v, zero_add, add_zero] using (affineTheta (s := (1/(12*k^2) : ℝ)) (by positivity) hg b
      (gramSchmidt ℝ b) floor diag (fun _ _ hij ↦ gramSchmidt_inv_triangular ℝ b hij) 0).1
  have partialSum := summ.sum_le_tsum (insert 0 S) (fun c _ ↦ (Real.exp_pos _).le)
  change (∑ c ∈ insert 0 S, F c) ≤ ∑' c, F c at partialSum
  rw [Finset.sum_insert zero_out, show F 0 = 1 by simp [F, v]] at partialSum
  have total := latticeTheta_le b (s := (1/(12*k^2) : ℝ)) (by positivity) hg floor
  change (∑' c, F c) ≤ _ at total
  change (∑ w ∈ A, jointWeight w) ≤ _
  rw [show g^2 / (12*k^2) = (1/(12*k^2))*g^2 by ring]
  linarith

private theorem weightNonneg (w : Fin N → Digit 3) : 0 ≤ jointWeight w := by
  unfold jointWeight weight
  positivity

/-- Upper Cantelli inequality, obtained by reflecting the observable. -/
theorem cantelliUpper {α : Type*} [Fintype α] (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (mass : ∑ x, p x = 1) (a : ℝ) (ha : 0 < a) :
    let m := ∑ x, p x * X x
    let v := ∑ x, p x * (X x - m)^2
    (∑ x with m+a ≤ X x, p x) ≤ v/(v+a^2) := by
  intro m v
  have bound := cantelli p (fun x ↦ -X x) hp mass a ha
  simp only [mul_neg, Finset.sum_neg_distrib] at bound
  change (∑ x with -X x ≤ -m-a, p x) ≤ _ at bound
  simp_rw [show ∀ x, (-X x ≤ -m-a) ↔ m+a ≤ X x by intro x; constructor <;> intro <;> linarith,
    show ∀ x, (-X x - -(∑ j, p j * X j))^2 = (X x-m)^2 by intro x; dsimp [m]; ring] at bound
  exact bound

private theorem energyCap (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) (w : Fin N → Digit 3) : ‖projectedCBD Q w‖^2 ≤ 9*N := by
  have sym : (1-Q).transpose = 1-Q := by simp [hs]
  have idem : (1-Q)*(1-Q) = 1-Q := by simp [sub_mul, mul_sub, hp]
  have nonneg := sq_nonneg ‖projectedCBD (1-Q) w‖
  rw [projectedCBD_norm_sq _ sym idem] at nonneg
  rw [projectedCBD_norm_sq _ hs hp]
  have eq : quadratic (1-Q) w = (∑ i, (centered (w i) : ℝ)^2) - quadratic Q w := by
    simp [quadratic, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, sq]
  rw [eq] at nonneg
  have each (i : Fin N) : (centered (w i) : ℝ)^2 ≤ 9 := by
    generalize w i = z
    fin_cases z <;> norm_num [centered]
  have := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ each i)
  simp at this
  linarith

/-- The horizontal lattice as an additive subgroup of the ambient space. -/
noncomputable def horizontalLattice (V : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (b : Module.Basis (Fin d) ℝ V) :=
  (Submodule.span ℤ (Set.range b)).toAddSubgroup.map V.subtype.toAddMonoidHom

noncomputable def thetaExcess (d : ℕ) (g k : ℝ) :=
  (∑' m : ℤ, Real.exp (-(g^2/(12*k^2))*(m : ℝ)^2))^d - 1

/-- CBD(3) mass of all-heights uniqueness for a fixed projection and horizontal lattice. -/
theorem uniquenessProbability (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) (trace : Q.trace = d)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (fixed : ∀ h : V, Q.mulVec (WithLp.ofLp h.val) = WithLp.ofLp h.val)
    (b : Module.Basis (Fin d) ℝ V) {g L : ℝ} (hg : 0 < g)
    (floor : ∀ i, g ≤ ‖gramSchmidt ℝ b i‖) (hL : 0 ≤ L)
    (minimum : ∀ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) → L ≤ ‖h‖)
    (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ)) :
    let a := L^2 - 1 - (3/2)*(d : ℝ)
    let v := (9/2)*(d : ℝ)
    1 - (v/(v+a^2) + thetaExcess d g 1 +
      ∑ k ∈ Finset.Icc 2 (Nat.sqrt (9*N+1)), thetaExcess d g k) ≤
      ∑ w with allHeightsUnique (horizontalLattice V b) (projectedCBD Q w), jointWeight w := by
  classical
  intro a v
  let m := (3/2)*(d : ℝ)
  let B := Submodule.span ℤ (Set.range b)
  let y := projectedCBD Q
  let U w := allHeightsUnique (horizontalLattice V b) (y w)
  let Z w := m+a ≤ quadratic Q w
  let O w := ∃ h ∈ B, h ≠ (0 : V) ∧ ‖y w + h.val‖ ≤ ‖y w‖
  let T (k : ℕ) w := ∃ h ∈ B, h ≠ (0 : V) ∧
    ‖h.val + (k : ℝ) • y w‖^2 + (k : ℝ)^2 ≤ ‖y w‖^2 + 1
  let S := Finset.Icc 2 (Nat.sqrt (9*N+1))
  let mass (P : (Fin N → Digit 3) → Prop) := ∑ w with P w, jointWeight w
  have cover w (hz : ¬Z w) (ho : ¬O w) (ht : ∀ k ∈ S, ¬T k w) : U w := by
    apply (allHeightsUniquenessCriterion _ _).2
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩ hn
      have hl := minimum h hh (fun eq ↦ hn (by simp [eq]))
      change ‖projectedCBD Q w‖^2 + 1 < ‖h‖^2
      rw [projectedCBD_norm_sq Q hs hp]
      change ¬ m+a ≤ quadratic Q w at hz
      dsimp [m,a] at hz
      nlinarith [sq_le_sq' (by linarith : -‖h‖ ≤ L) hl]
    · rintro _ ⟨h, hh, rfl⟩ hn
      have lt : ‖y w‖ < ‖y w + h.val‖ := lt_of_not_ge fun e ↦
        ho ⟨h, hh, fun eq ↦ hn (by simp [eq]), e⟩
      change ‖y w‖^2 < ‖h.val + y w‖^2
      rw [add_comm]
      exact pow_lt_pow_left₀ lt (norm_nonneg _) (by decide)
    · intro k hk hcap
      lift k to ℕ using (by omega)
      rintro _ ⟨h, hh, rfl⟩
      push_cast at hcap ⊢
      have bound : (k : ℝ)^2 ≤ 9*N+1 := by linarith [energyCap Q hs hp w]
      have mem : k ∈ S := Finset.mem_Icc.mpr ⟨by omega, Nat.le_sqrt'.mpr (by exact_mod_cast bound)⟩
      by_contra! hit
      have hit' : ‖h.val + (k : ℝ) • y w‖^2 + (k : ℝ)^2 ≤ ‖y w‖^2 + 1 := by
        rw [Nat.cast_smul_eq_nsmul ℝ]
        change ‖h.val + (k : ℤ) • y w‖^2 ≤ ‖y w‖^2 + 1 - (k : ℝ)^2 at hit
        simp only [natCast_zsmul] at hit
        linarith
      have hn := (highHit _ _ _ (by exact_mod_cast (show 2 ≤ k by omega)) hit').1
      exact ht k mem ⟨h, hh, fun eq ↦ hn (by simp [eq]), hit'⟩
  have sumBound : 1 ≤ mass U + mass Z + mass O + ∑ k ∈ S, mass (T k) := by
    rw [← joint_mass (N := N)]
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm (s := S)]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    have pos (P : Prop) [Decidable P] : 0 ≤ (if P then jointWeight w else 0) := by
      split <;> simp [weightNonneg]
    have nonneg := Finset.sum_nonneg (s := S) (fun k _ ↦ pos (T k w))
    by_cases hu : U w
    · simp [hu]; linarith [pos (Z w), pos (O w)]
    by_cases hz : Z w
    · simp [hu,hz]; linarith [pos (O w)]
    by_cases ho : O w
    · simp [hu,hz,ho,nonneg]
    have ex : ∃ k ∈ S, T k w := by by_contra! no; exact hu (cover w hz ho no)
    obtain ⟨k,hk,hit⟩ := ex
    simpa [hu,hz,ho,hit] using Finset.single_le_sum (fun j _ ↦ pos (T j w)) hk
  have hzero := cantelliUpper jointWeight (quadratic Q) weightNonneg joint_mass a gap
  simp only [quadratic_mean, trace] at hzero
  let var := ∑ w, jointWeight w * (quadratic Q w-m)^2
  have hv : 0 ≤ var := Finset.sum_nonneg fun w _ ↦ mul_nonneg (weightNonneg _) (sq_nonneg _)
  have hv' : var ≤ v := by simpa [var,m,v,trace] using projection_variance_le Q hs hp
  have bz : mass Z ≤ v/(v+a^2) := by
    apply (show mass Z ≤ var/(var+a^2) from hzero).trans
    apply (div_le_div_iff₀ (by positivity) (by dsimp [v]; positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hv' (sq_nonneg a)]
  have bo : mass O ≤ thetaExcess d g 1 := by
    simpa [mass,O,B,y,thetaExcess] using heightOneUnion Q hs V fixed b hg floor
  have bt := Finset.sum_le_sum (s := S) (fun k hk ↦
    (show mass (T k) ≤ thetaExcess d g k from highUnion Q hs V fixed b hg floor k
      (by exact_mod_cast (Finset.mem_Icc.mp hk).1)))
  change 1 - _ ≤ mass U
  linarith

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.uniquenessProbability
