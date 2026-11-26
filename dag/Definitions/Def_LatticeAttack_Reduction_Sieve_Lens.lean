module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Geometry

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Real MeasureTheory Metric Set

/-- The Euclidean shell in axial and orthogonal coordinates, centered at axial coordinate c. -/
def axialShell {F : Type*} [Norm F] (R w c : ℝ) : Set (ℝ × F) :=
  {p | (R*(1-w))^2 ≤ (p.1-c)^2 + ‖p.2‖^2 ∧ (p.1-c)^2 + ‖p.2‖^2 ≤ (R*(1+w))^2}

/-- A cylinder about the perpendicular bisector lies in both shells.
Its cross section is an annulus of outer radius b. -/
theorem lensCylinder_subset {F : Type*} [NormedAddCommGroup F] {R w d b : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hd : 0 ≤ d) (hb : 0 ≤ b) (he : d^2+b^2=R^2) :
    Icc ((1-w)*d) ((1+w)*d) ×ˢ
      (closedBall (0:F) b \ closedBall 0 ((1-w)*b)) ⊆
      axialShell R w 0 ∩ axialShell R w (2*d) := by
  intro p hp
  obtain ⟨⟨hx, hx'⟩,hy,hy'⟩ := hp
  rw [mem_closedBall, dist_zero_right] at hy hy'
  have hylo : (1-w)*b ≤ ‖p.2‖ := le_of_lt (lt_of_not_ge hy')
  have hyhi : ‖p.2‖ ≤ (1+w)*b := by simpa [add_mul] using hy.trans (le_add_of_nonneg_right (mul_nonneg hw hb))
  have H (z : ℝ) (h : (1-w)*d ≤ z) (h' : z ≤ (1+w)*d) :
      (R*(1-w))^2 ≤ z^2+‖p.2‖^2 ∧ z^2+‖p.2‖^2 ≤ (R*(1+w))^2 := by
    have d0 := mul_nonneg (sub_nonneg.mpr hw') hd
    constructor
    · nlinarith only [pow_le_pow_left₀ d0 h 2,
        pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hw') hb) hylo 2,
        congrArg (· * (1-w)^2) he]
    · nlinarith only [pow_le_pow_left₀ (d0.trans h) h' 2,
        pow_le_pow_left₀ (norm_nonneg p.2) hyhi 2, congrArg (· * (1+w)^2) he]
  constructor
  · simpa [axialShell] using H _ hx hx'
  · have hh := H (2*d-p.1) (by linarith) (by linarith)
    simpa [axialShell, sub_sq_comm (p.1) (2*d)] using hh

/-- Absolute volume of the lens, in dimension k+1. -/
theorem lensVolume_lower {k : ℕ} (hk : 1 ≤ k) {R w d b : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hd : 0 ≤ d) (hb : 0 ≤ b) (he : d^2+b^2=R^2) :
    let F := EuclideanSpace ℝ (Fin k)
    2*w*d * (w * volume.real (closedBall (0:F) b)) ≤
      volume.real (axialShell (F:=F) R w 0 ∩ axialShell R w (2*d)) := by
  dsimp only
  let F := EuclideanSpace ℝ (Fin k)
  let T := axialShell (F:=F) R w 0 ∩ axialShell R w (2*d)
  let s := |R*(1+w)|
  have hsub : T ⊆ closedBall (0 : ℝ × F) s := by
    intro p hp
    have hh := hp.1.2
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    dsimp [s]
    simp only [sub_zero] at hh
    constructor
    · nlinarith [sq_abs (R*(1+w)), sq_abs p.1, abs_nonneg (R*(1+w)), abs_nonneg p.1,
        sq_nonneg ‖p.2‖]
    · nlinarith [sq_abs (R*(1+w)), abs_nonneg (R*(1+w)), norm_nonneg p.2, sq_nonneg p.1]
  apply le_trans _ (measureReal_mono (lensCylinder_subset hw hw' hd hb he)
    (measure_ne_top_of_subset hsub measure_closedBall_lt_top.ne))
  rw [Measure.volume_eq_prod, measureReal_prod_prod, Real.volume_real_Icc_of_le (by
    nlinarith [mul_nonneg hw hd]), show (1+w)*d-(1-w)*d=2*w*d by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [measureReal_sdiff (closedBall_subset_closedBall (by nlinarith [mul_nonneg hw hb]))
    measurableSet_closedBall measure_closedBall_lt_top.ne, measureReal_def (s := closedBall _ (_*_)),
    Measure.addHaar_closedBall_mul volume _ (sub_nonneg.mpr hw') hb, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
  simp only [finrank_euclideanSpace_fin]
  have hp : (1-w)^k ≤ 1-w := by
    simpa using pow_le_pow_of_le_one (sub_nonneg.mpr hw') (by linarith : 1-w ≤ 1) hk
  nlinarith [mul_le_mul_of_nonneg_right hp (measureReal_nonneg (μ:=volume) (s:=closedBall (0:F) b))]

private theorem axialShell_subset_box {F : Type*} [NormedAddCommGroup F] {R w : ℝ}
    (h : 0 ≤ R*(1+w)) :
    axialShell (F := F) R w 0 ⊆ Icc (-(R*(1+w))) (R*(1+w)) ×ˢ closedBall 0 (R*(1+w)) := by
  intro p hp
  have hh := hp.2
  simp only [sub_zero] at hh
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg ‖p.2‖]
  · nlinarith [sq_nonneg ‖p.2‖]
  · rw [mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg p.1]

/-- Relative lower bound for the actual intersection in axial coordinates.
The loss from replacing the shell by its enclosing cylinder is explicit. -/
theorem lensVolume_relative {k : ℕ} (hk : 1 ≤ k) {R w g q : ℝ}
    (hR : 0 ≤ R) (hw : 0 ≤ w) (hw' : w ≤ 1) (hg : 0 ≤ g) (hq : 0 ≤ q)
    (he : (g/2)^2+q^2=1) :
    let F := EuclideanSpace ℝ (Fin k)
    (w^2*g*q^k) * volume.real (axialShell (F:=F) R w 0) ≤
      (2*(1+w)^(k+1)) * volume.real
        (axialShell (F:=F) R w 0 ∩ axialShell R w (g*R)) := by
  dsimp only
  let F := EuclideanSpace ℝ (Fin k)
  let B := volume.real (closedBall (0:F) R)
  have scale (a : ℝ) (ha : 0 ≤ a) : volume.real (closedBall (0:F) (a*R)) = a^k * B := by
    rw [measureReal_def, Measure.addHaar_closedBall_mul volume _ ha hR, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    simp [F, B, measureReal_def]
  have hoff : 0 ≤ R*(1+w) := by positivity
  have hupper := measureReal_mono (μ := volume) (axialShell_subset_box (F:=F) hoff)
    (h₂ := by rw [Measure.volume_eq_prod, Measure.prod_prod]; exact ENNReal.mul_ne_top isCompact_Icc.measure_lt_top.ne measure_closedBall_lt_top.ne)
  rw [Measure.volume_eq_prod, measureReal_prod_prod, Real.volume_real_Icc_of_le (by linarith),
    mul_comm R (1+w), scale _ (by positivity)] at hupper
  have hlow := lensVolume_lower hk hw hw' (show 0 ≤ g/2*R by positivity)
    (show 0 ≤ q*R by positivity) (R:=R) (by nlinarith only [congrArg (· * R^2) he])
  dsimp only at hlow
  rw [scale q hq, show 2*(g/2*R) = g*R by ring] at hlow
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ w^2*g*q^k)
    _ = 2*(1+w)^(k+1) * (2*w*(g/2*R)*(w*(q^k*B))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- Volume is invariant under passage to axial coordinates. -/
theorem axialShell_volume (k : ℕ) {R w : ℝ} (hR : 0 ≤ R) (hw : 0 ≤ w) (hw' : w ≤ 1) :
    volume.real (axialShell (F:=EuclideanSpace ℝ (Fin k)) R w 0) =
      volume.real (radialShell (E:=EuclideanSpace ℝ (Fin (k+1))) R w) := by
  let F := EuclideanSpace ℝ (Fin k)
  let E := WithLp 2 (ℝ × F)
  have hd : Module.finrank ℝ E = k+1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × F)).finrank_eq, Module.finrank_prod]
    simp [F, Nat.add_comm]
  let e := ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr
  have hh : WithLp.ofLp ⁻¹' (axialShell (F:=F) R w 0) =
      e ⁻¹' (radialShell R w) := by
    ext z
    change ((R*(1-w))^2 ≤ _ ∧ _ ≤ (R*(1+w))^2) ↔
      R*(1-w) ≤ ‖e z‖ ∧ ‖e z‖ ≤ R*(1+w)
    rw [e.norm_map]
    have hs := WithLp.prod_norm_sq_eq_of_L2 z
    simp only [Real.norm_eq_abs, sq_abs] at hs
    change ‖z‖^2 = (WithLp.ofLp z).1^2 + ‖(WithLp.ofLp z).2‖^2 at hs
    simp only [sub_zero, ← hs]
    constructor <;> intro ⟨h₁,h₂⟩ <;> constructor <;>
      nlinarith [norm_nonneg z, mul_nonneg hR (sub_nonneg.mpr hw'), mul_nonneg hR (by linarith : 0 ≤ 1+w)]
  apply congrArg ENNReal.toReal
  calc
    _ = volume (WithLp.ofLp ⁻¹' axialShell (F:=F) R w 0) :=
      ((WithLp.volume_preserving_ofLp ℝ F).measure_preimage_emb
        (MeasurableEquiv.toLp 2 (ℝ × F)).symm.measurableEmbedding _).symm
    _ = _ := by rw [hh]; exact e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding _

open scoped Pointwise in
theorem radialShell_scale (n : ℕ) (a R w : ℝ) (ha : 0 < a) :
    volume.real (radialShell (E:=EuclideanSpace ℝ (Fin n)) (a*R) w) =
      a^n * volume.real (radialShell (E:=EuclideanSpace ℝ (Fin n)) R w) := by
  let E := EuclideanSpace ℝ (Fin n)
  have eq : radialShell (E:=E) (a*R) w = a • radialShell R w := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    change (_ ≤ ‖x‖ ∧ ‖x‖ ≤ _) ↔ (_ ≤ ‖a⁻¹ • x‖ ∧ ‖a⁻¹ • x‖ ≤ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), ← div_eq_inv_mul,
      le_div_iff₀ ha, div_le_iff₀ ha]
    constructor <;> intro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [eq, measureReal_def, Measure.addHaar_smul_of_nonneg volume ha.le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp [measureReal_def]

#print axioms lensCylinder_subset
#print axioms lensVolume_lower
#print axioms lensVolume_relative
#print axioms axialShell_volume
#print axioms radialShell_scale

end SigabaNeo.Lattices.Sieve
