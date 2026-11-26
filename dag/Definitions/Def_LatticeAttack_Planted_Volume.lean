module

public import Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

public section

namespace SigabaNeo.Planted

open MeasureTheory Metric Set

/-- Half-open cubes of side one centered at the integer points fit in the enlarged ball. -/
theorem integerBall_card_le_volume {ι : Type*} [Fintype ι] (R : ℝ) (hR : 0 ≤ R) :
    ((integerBall (ι := ι) R).card : ℝ) ≤
      (R + Real.sqrt (Fintype.card ι) / 2) ^ Fintype.card ι *
        volume.real (ball (0 : EuclideanSpace ℝ ι) 1) := by
  classical
  let T := integerBall (ι := ι) R
  let cube (z : ι → ℤ) := univ.pi (fun i ↦ Ico ((z i : ℝ)-1/2) ((z i : ℝ)+1/2))
  have meas z : MeasurableSet (cube z) := (measurableSet_pi (to_countable _)).2 (.inl fun _ _ ↦ measurableSet_Ico)
  have vol z : volume (cube z) = 1 := by
    norm_num [cube, volume_pi_pi, Real.volume_Ico]
  have disj : PairwiseDisjoint (T : Set (ι → ℤ)) cube := by
    intro z _ w _ hne
    apply Set.disjoint_left.mpr
    intro x hz hw
    apply hne
    ext i
    obtain ⟨a,b⟩ := hz i (mem_univ i)
    obtain ⟨c,d⟩ := hw i (mem_univ i)
    change (z i : ℝ)-1/2 ≤ x i at a
    change x i < (z i : ℝ)+1/2 at b
    change (w i : ℝ)-1/2 ≤ x i at c
    change x i < (w i : ℝ)+1/2 at d
    have h₁ : z i < w i + 1 := by exact_mod_cast (by linarith : (z i : ℝ) < w i + 1)
    have h₂ : w i < z i + 1 := by exact_mod_cast (by linarith : (w i : ℝ) < z i + 1)
    omega
  let r := R + Real.sqrt (Fintype.card ι) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let D := closedBall (0 : EuclideanSpace ℝ ι) r
  have incl : (⋃ z ∈ T, cube z) ⊆ WithLp.toLp 2 ⁻¹' D := by
    intro x hx
    obtain ⟨z,hz,hx⟩ := mem_iUnion₂.mp hx
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i ↦ (z i : ℝ))
    let y : EuclideanSpace ℝ ι := WithLp.toLp 2 x
    have hv : ‖v‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      exact ((mem_integerBall hR z).mp hz).2
    have hd : ‖y-v‖ ≤ Real.sqrt (Fintype.card ι) / 2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [EuclideanSpace.real_norm_sq_eq, div_pow, Real.sq_sqrt (by positivity)]
      calc
        _ ≤ ∑ _ : ι, (1/2 : ℝ)^2 := by
          apply Finset.sum_le_sum
          intro i _
          obtain ⟨hl,hu⟩ := hx i (mem_univ i)
          change (z i : ℝ)-1/2 ≤ x i at hl
          change x i < (z i : ℝ)+1/2 at hu
          change (x i - (z i : ℝ))^2 ≤ _
          apply sq_le_sq' <;> linarith
        _ = _ := by simp; ring
    change dist y 0 ≤ r
    rw [dist_zero_right]
    exact (norm_le_norm_sub_add y v).trans (by dsimp [r]; linarith)
  have hvol := measure_mono (μ := volume) incl
  rw [measure_biUnion_finset disj (fun z _ ↦ meas z),
    (PiLp.volume_preserving_toLp ι).measure_preimage measurableSet_closedBall.nullMeasurableSet] at hvol
  simp only [vol, Finset.sum_const, nsmul_eq_mul, mul_one] at hvol
  have hh := ENNReal.toReal_mono (measure_closedBall_lt_top.ne) hvol
  change _ ≤ volume.real (closedBall (0 : EuclideanSpace ℝ ι) r) at hh
  simpa [Measure.addHaar_real_closedBall volume _ hr, r] using hh

#print axioms integerBall_card_le_volume

/-- Probability of an independent short vector for a uniform public matrix and fixed planting. -/
theorem badMatrices_probability {m n q : ℕ} [Fact q.Prime] (e : Fin m → ℤ) (s : Fin n → ℤ)
    (R B : ℝ) (hR : 0 ≤ R) (he : ∀ i, |(e i : ℝ)| ≤ B) (hs : ∀ j, |(s j : ℝ)| ≤ B)
    (hq : R * Real.sqrt (1+B^2) < q) :
    let d := m+n+1
    let V := volume.real (ball (0 : EuclideanSpace ℝ (Coord m n)) 1)
    let G := ((q : ℝ)^m / V) ^ (d : ℝ)⁻¹
    ((badMatrices q e s R).card : ℝ) / (q : ℝ)^(n*m) ≤ ((R + Real.sqrt d / 2) / G)^d := by
  intro d V G
  have hqp : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hv : 0 < V := ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
    measure_ball_lt_top.ne
  have hd : Fintype.card (Coord m n) = d := by simp [Coord,d,Nat.add_assoc]
  have hcount : ((badMatrices q e s R).card : ℝ) * (q : ℝ)^m ≤
      (integerBall (ι := Coord m n) R).card * (q : ℝ)^(n*m) := by
    exact_mod_cast badMatrices_card e s R B hR he hs hq
  have hvol := integerBall_card_le_volume (ι := Coord m n) R hR
  rw [hd] at hvol
  change _ ≤ _ * V at hvol
  rw [div_pow, show G^d = (q : ℝ)^m / V from
    Real.rpow_inv_natCast_pow (by positivity) (by dsimp [d]; omega), div_div_eq_mul_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact hcount.trans (mul_le_mul_of_nonneg_right hvol (by positivity))

#print axioms badMatrices_probability

end SigabaNeo.Planted
