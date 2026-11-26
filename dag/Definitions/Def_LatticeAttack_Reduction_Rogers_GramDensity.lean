module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_Gram

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace SigabaNeo.Rogers.Gram

/-- Each transverse radius occurs in exactly s-1 off-diagonal coordinates. -/
theorem angular_jacobian_product {s : ℕ} (r : Fin s → ℝ) :
    (∏ ij : OffDiagonal s, r ij.val.1 * r ij.val.2) = (∏ i, r i) ^ (s-1) := by
  classical
  have expand (f : Fin s × Fin s → ℝ) :
      (∏ ij : OffDiagonal s, f ij.val) = ∏ ij : Fin s × Fin s,
        if ij.1 < ij.2 then f ij else 1 := by
    rw [← Finset.prod_filter, Finset.prod_subtype (p := fun ij : Fin s × Fin s ↦ ij.1 < ij.2) _ (by simp) f]
  rw [Finset.prod_mul_distrib, expand (fun ij ↦ r ij.1), expand (fun ij ↦ r ij.2),
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ j : Fin s, if j ≠ i then r i else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      rcases lt_trichotomy i j with hij | rfl | hji <;> simp_all [ne_of_gt, ne_of_lt] <;> omega
    _ = _ := by
      rw [← Finset.prod_filter]
      simp [Finset.filter_ne']

#print axioms angular_jacobian_product

theorem angular_block_posDef {s : ℕ} (B : Matrix Unit (Fin s) ℝ)
    (r : Fin s → ℝ) (hr : ∀ i, 0 < r i) (H : Matrix (Fin s) (Fin s) ℝ) :
    (Matrix.fromBlocks 1 B B.transpose
      (B.transpose * B + Matrix.diagonal r * H * Matrix.diagonal r)).PosDef ↔ H.PosDef := by
  let D := Matrix.diagonal r
  have hdet : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  have hu : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [D, Matrix.det_diagonal] using hdet.ne'
  have hconj := Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := H) hu
  let := invertibleOne (α := Matrix Unit Unit ℝ)
  have hschur := Matrix.PosDef.fromBlocks₁₁ B (B.transpose * B + D * H * D)
    (Matrix.PosDef.one : (1 : Matrix Unit Unit ℝ).PosDef)
  simp [Matrix.star_eq_conjTranspose, D] at hconj hschur
  by_cases h : H.PosSemidef
  · rw [(hschur.mpr (hconj.mpr h)).posDef_iff_det_ne_zero, h.posDef_iff_det_ne_zero,
      angular_block_det]
    simp [hdet.ne']
  · exact iff_of_false (fun hp ↦ h (hconj.mp (hschur.mp hp.posSemidef))) (fun hp ↦ h hp.posSemidef)

#print axioms angular_block_posDef

/-- The ambient Gram density times the fiber Jacobian, on a positive-definite fiber. -/
theorem angular_density_pullback (m k : ℕ) (hm : 0 < m)
    (B : Matrix Unit (Fin (k+1)) ℝ) (r : Fin (k+1) → ℝ) (hr : ∀ i, 0 < r i)
    (H : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hH : H.PosDef) :
    let p := ((m : ℝ) - k - 2) / 2
    let G := Matrix.fromBlocks 1 B B.transpose
      (B.transpose * B + Matrix.diagonal r * H * Matrix.diagonal r)
    gramConstant (m+1) (k+2) * G.det ^ p *
        (∏ ij : OffDiagonal (k+1), r ij.val.1 * r ij.val.2) =
      normalizer (((m : ℝ)+1-3)/2)^(k+1) * (∏ i, r i) ^ ((m : ℝ)-2) *
        (gramConstant m (k+1) * H.det ^ p) := by
  intro p G
  have hr' : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  dsimp only [G]
  rw [angular_block_det, angular_jacobian_product, gramConstant_recursion m k hm,
    Real.mul_rpow (sq_nonneg _) hH.det_pos.le, Nat.add_sub_cancel,
    ← Real.rpow_natCast_mul hr'.le, ← Real.rpow_natCast (∏ i, r i) k]
  have he : (m : ℝ) - 2 = (2 : ℕ) * p + k := by dsimp [p]; ring
  rw [he, Real.rpow_add hr']
  ring

#print axioms angular_density_pullback

def gramDomain (s : ℕ) := {x : OffDiagonal s → ℝ | (correlation x).PosSemidef}

private theorem measurable_gramDomain (s : ℕ) : MeasurableSet (gramDomain s) := by
  have hc : Continuous (@correlation s) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold correlation
    split_ifs <;> fun_prop
  have he : gramDomain s =
      {x | (correlation x).conjTranspose = correlation x} ∩
      ⋂ v : Fin s → ℝ, {x | 0 ≤ dotProduct v ((correlation x).mulVec v)} := by
    ext x
    simp [gramDomain, Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [he]
  exact ((isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun v ↦
    isClosed_le continuous_const (continuous_const.dotProduct
      (hc.matrix_mulVec continuous_const)))).measurableSet

def gramKernel (s : ℕ) (p : ℝ) : Measure (OffDiagonal s → ℝ) :=
  (volume.restrict (gramDomain s)).withDensity (fun x ↦ ENNReal.ofReal ((correlation x).det ^ p))

def gramLaw (n s : ℕ) : Measure (OffDiagonal s → ℝ) :=
  Measure.map (fun z : Fin s → Sphere n ↦ fun ij : OffDiagonal s ↦
    inner ℝ (z ij.val.1 : Ambient n) (z ij.val.2 : Ambient n)) (Measure.pi fun _ ↦ uniform n)

/-- Disintegration with the lower-dimensional Gram law as the inner measure. -/
theorem gramLaw_fiber_integral {m s : ℕ} (hm : 0 < m)
    (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y : Sphere (m+1) × (Fin s → Sphere (m+1)),
      F (fun i ↦ inner ℝ (y.1 : Ambient (m+1)) (y.2 i),
        fun ij ↦ inner ℝ (y.2 ij.val.1 : Ambient (m+1)) (y.2 ij.val.2))
      ∂(uniform (m+1)).prod (Measure.pi fun _ ↦ uniform (m+1))) =
    ∫⁻ a : Fin s → ℝ, ∫⁻ x, F (a, fun ij ↦ angularThird (a ij.val.1) (a ij.val.2) (x ij))
      ∂gramLaw m s ∂Measure.pi (fun _ ↦ volume.withDensity (weight (((m:ℝ)+1-3)/2))) := by
  let ρ := volume.withDensity (weight (((m:ℝ)+1-3)/2))
  let ν := (uniform m).map Subtype.val
  let := uniform_probability hm
  have : IsProbabilityMeasure ρ := ⟨by
    rw [show ρ = _ from rfl, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      weight_integral]
    have : 0 < (m : ℝ) := by exact_mod_cast hm
    linarith⟩
  let split := measurePreserving_arrowProdEquivProdArrow ℝ (Ambient m) (Fin s)
    (fun _ ↦ ρ) (fun _ ↦ ν)
  let T := fun (w : (Fin s → ℝ) × (Fin s → Ambient m)) ↦ F (w.1, fun ij ↦
    angularThird (w.1 ij.val.1) (w.1 ij.val.2) (inner ℝ (w.2 ij.val.1) (w.2 ij.val.2)))
  have hT : Measurable T := by dsimp [T, angularThird]; fun_prop
  rw [gram_angular_recursion hm F hF]
  change (∫⁻ w, T ((MeasurableEquiv.arrowProdEquivProdArrow ℝ (Ambient m) (Fin s)) w) ∂_) = _
  rw [split.lintegral_comp hT, lintegral_prod _ hT.aemeasurable]
  apply lintegral_congr
  intro a
  have hval : MeasurePreserving (Subtype.val : Sphere m → Ambient m) (uniform m) ν :=
    ⟨measurable_subtype_coe, rfl⟩
  have hv := measurePreserving_pi (fun _ : Fin s ↦ uniform m) (fun _ ↦ ν) (fun _ ↦ hval)
  rw [← hv.lintegral_comp (f := fun z ↦ T (a,z)) (hT.comp (measurable_const.prodMk measurable_id)),
    gramLaw, lintegral_map (by dsimp [angularThird]; fun_prop) (by fun_prop)]

#print axioms gramLaw_fiber_integral

/-- Split off the coordinates involving index zero from the remaining pairs. -/
def poleIndex (s : ℕ) : Fin s ⊕ OffDiagonal s ≃ OffDiagonal (s+1) where
  toFun := Sum.elim (fun i ↦ ⟨(0,i.succ), Fin.succ_pos _⟩)
    (fun ij ↦ ⟨(ij.val.1.succ,ij.val.2.succ), Fin.succ_lt_succ_iff.mpr ij.property⟩)
  invFun := fun ⟨(i,j),h⟩ ↦ by
    cases j using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero _ h)
    | succ j =>
      cases i using Fin.cases with
      | zero => exact Sum.inl j
      | succ i => exact Sum.inr ⟨(i,j), Fin.succ_lt_succ_iff.mp h⟩
  left_inv := by rintro (i | ⟨⟨i,j⟩,h⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨i,j⟩,h⟩
    cases j using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero _ h)
    | succ j => cases i using Fin.cases <;> rfl

def splitGram (s : ℕ) : (OffDiagonal (s+1) → ℝ) ≃ᵐ (Fin s → ℝ) × (OffDiagonal s → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (poleIndex s)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi _)

theorem splitGram_volume (s : ℕ) : MeasurePreserving (splitGram s) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi _).comp
    (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) (poleIndex s)).symm

def poleRowIndex (s : ℕ) : Unit ⊕ Fin s ≃ Fin (s+1) where
  toFun := Sum.elim (fun _ ↦ 0) Fin.succ
  invFun := Fin.cases (.inl ()) (.inr ·)
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by intro i; cases i using Fin.cases <;> rfl

/-- In the axial chart, the correlation matrix is the Schur block matrix. -/
theorem correlation_splitGram {s : ℕ} (a r : Fin s → ℝ)
    (hr : ∀ i, a i ^ 2 + r i ^ 2 = 1) (x : OffDiagonal s → ℝ) :
    let B : Matrix Unit (Fin s) ℝ := fun _ i ↦ a i
    let y := fun ij : OffDiagonal s ↦ a ij.val.1 * a ij.val.2 +
      (r ij.val.1 * r ij.val.2) * x ij
    (correlation ((splitGram s).symm (a,y))).submatrix (poleRowIndex s) (poleRowIndex s) =
      Matrix.fromBlocks 1 B B.transpose
        (B.transpose * B + Matrix.diagonal r * correlation x * Matrix.diagonal r) := by
  intro B y
  apply Matrix.ext
  rintro (u | i) (v | j)
  · rfl
  · change correlation ((splitGram s).symm (a,y)) 0 j.succ = a j
    rw [correlation, dite_eq_left (Fin.succ_pos _)]
    rfl
  · change correlation ((splitGram s).symm (a,y)) i.succ 0 = a i
    rw [correlation, dite_eq_right (Fin.not_lt_zero _), dite_eq_left (Fin.succ_pos _)]
    rfl
  · change correlation ((splitGram s).symm (a,y)) i.succ j.succ =
      (B.transpose * B + Matrix.diagonal r * correlation x * Matrix.diagonal r) i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Fintype.sum_unique]
    change correlation _ i.succ j.succ = a i * a j + r i * correlation x i j * r j
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [correlation, Fin.succ_lt_succ_iff, h, dite_true]
      change a i * a j + (r i * r j) * x _ = _
      ring
    · simp [correlation]
      nlinarith [hr i]
    · simp only [correlation, Fin.succ_lt_succ_iff, h, h.not_gt, dite_false, dite_true]
      change a j * a i + (r j * r i) * x _ = _
      ring

#print axioms correlation_splitGram

open Classical in
def gramDensity {s : ℕ} (n : ℕ) (x : OffDiagonal s → ℝ) : ℝ :=
  if (correlation x).PosDef then gramConstant n s * (correlation x).det ^ (((n:ℝ)-s-1)/2)
  else 0

/-- Pointwise change of density in the actual off-diagonal coordinates, including
singular and indefinite transverse matrices. -/
theorem gramDensity_fiber (m k : ℕ) (hm : 0 < m) (a r : Fin (k+1) → ℝ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i, a i ^ 2 + r i ^ 2 = 1) (x : OffDiagonal (k+1) → ℝ) :
    let y := fun ij : OffDiagonal (k+1) ↦ a ij.val.1 * a ij.val.2 +
      (r ij.val.1 * r ij.val.2) * x ij
    gramDensity (m+1) ((splitGram (k+1)).symm (a,y)) *
        (∏ ij : OffDiagonal (k+1), r ij.val.1 * r ij.val.2) =
      normalizer (((m:ℝ)+1-3)/2)^(k+1) * (∏ i, r i) ^ ((m:ℝ)-2) * gramDensity m x := by
  intro y
  let G := correlation ((splitGram (k+1)).symm (a,y))
  let B : Matrix Unit (Fin (k+1)) ℝ := fun _ i ↦ a i
  let e := poleRowIndex (k+1)
  have hblock := correlation_splitGram a r ha x
  have hs : G.PosDef ↔ (G.submatrix e e).PosDef := by
    refine ⟨fun h ↦ h.submatrix e.injective, fun h ↦ ?_⟩
    simpa [Matrix.submatrix_submatrix] using h.submatrix e.symm.injective
  have hpd : G.PosDef ↔ (correlation x).PosDef := by
    rw [hs]
    rw [show G.submatrix e e = _ from hblock]
    exact angular_block_posDef B r hr _
  unfold gramDensity
  by_cases hx : (correlation x).PosDef
  · rw [ite_eq_left hx, ite_eq_left (hpd.mpr hx)]
    change gramConstant _ _ * G.det ^ _ * _ = _
    rw [← Matrix.det_submatrix_equiv_self e G, show G.submatrix e e = _ from hblock]
    push_cast
    rw [show ((m:ℝ)+1-(k+1+1)-1)/2 = (m-k-2)/2 by ring,
      show ((m:ℝ)-(k+1)-1)/2 = (m-k-2)/2 by ring]
    exact angular_density_pullback m k hm B r hr (correlation x) hx
  · rw [ite_eq_right hx, ite_eq_right (hpd.not.mpr hx), zero_mul, mul_zero]

#print axioms gramDensity_fiber

private theorem measurable_gramDensity (n s : ℕ) : Measurable (@gramDensity s n) := by
  classical
  have hc : Continuous (@correlation s) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold correlation
    split_ifs <;> fun_prop
  have hp : {x : OffDiagonal s → ℝ | (correlation x).PosDef} =
      gramDomain s ∩ {x | (correlation x).det ≠ 0} := by
    ext x
    exact ⟨fun h ↦ ⟨h.posSemidef, h.det_pos.ne'⟩, fun ⟨h,hd⟩ ↦
      (show (correlation x).PosSemidef from h).posDef_iff_det_ne_zero.mpr hd⟩
  have hd := hc.matrix_det.measurable
  apply Measurable.ite _ (by fun_prop) measurable_const
  rw [hp]
  exact (measurable_gramDomain s).inter (isClosed_eq hc.matrix_det continuous_const).measurableSet.compl

theorem gramDensity_fiber_integral (m k : ℕ) (hm : 0 < m) (a r : Fin (k+1) → ℝ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i, a i ^ 2 + r i ^ 2 = 1)
    (F : (OffDiagonal (k+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    let T := fun (x : OffDiagonal (k+1) → ℝ) ij ↦ a ij.val.1 * a ij.val.2 +
      (r ij.val.1 * r ij.val.2) * x ij
    (∫⁻ y, ENNReal.ofReal (gramDensity (m+1) ((splitGram (k+1)).symm (a,y))) * F y) =
      ∫⁻ x, ENNReal.ofReal (normalizer (((m:ℝ)+1-3)/2)^(k+1) *
        (∏ i, r i) ^ ((m:ℝ)-2) * gramDensity m x) * F (T x) := by
  intro T
  let J := ∏ ij : OffDiagonal (k+1), r ij.val.1 * r ij.val.2
  have hJ : 0 < J := Finset.prod_pos fun i _ ↦ mul_pos (hr _) (hr _)
  let K := fun y ↦ ENNReal.ofReal (gramDensity (m+1) ((splitGram (k+1)).symm (a,y))) * F y
  have hK : Measurable K := ((measurable_gramDensity _ _).comp
    ((splitGram _).symm.measurable.comp (measurable_const.prodMk measurable_id))).ennreal_ofReal.mul hF
  have he : (∫⁻ x, K (T x)) = ENNReal.ofReal J⁻¹ * ∫⁻ y, K y := by
    rw [← lintegral_map hK (by dsimp [T]; fun_prop), angular_fiber_volume a r hr,
      lintegral_smul_measure, smul_eq_mul]
  change (∫⁻ y, K y) = _
  calc
    _ = ENNReal.ofReal J * ∫⁻ x, K (T x) := by
      rw [he, ← mul_assoc, ← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne']
      simp
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← gramDensity_fiber m k hm a r hr ha x, mul_comm (gramDensity _ _),
        ENNReal.ofReal_mul hJ.le, mul_assoc]

#print axioms gramDensity_fiber_integral

theorem gramLaw_recursion {m s : ℕ} (hm : 0 < m)
    (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (splitGram s x) ∂gramLaw (m+1) (s+1)) =
    ∫⁻ a : Fin s → ℝ, ∫⁻ x, F (a, fun ij ↦ angularThird (a ij.val.1) (a ij.val.2) (x ij))
      ∂gramLaw m s ∂Measure.pi (fun _ ↦ volume.withDensity (weight (((m:ℝ)+1-3)/2))) := by
  let := uniform_probability (n := m+1) (by omega)
  have : SigmaFinite (uniform (m+1)) := inferInstance
  have : ∀ _ : Fin (s+1), SigmaFinite (uniform (m+1)) := fun _ ↦ ‹_›
  let split := measurePreserving_piFinSuccAbove (fun _ : Fin (s+1) ↦ uniform (m+1)) 0
  rw [← gramLaw_fiber_integral hm F hF, ← split.lintegral_comp (by fun_prop),
    gramLaw, lintegral_map (f := fun x ↦ F (splitGram s x)) (hF.comp (splitGram s).measurable) (by fun_prop)]
  apply lintegral_congr
  intro z
  change F (_,_) = F (_,_)
  congr 1

#print axioms splitGram_volume
#print axioms gramLaw_recursion

/-- Euclidean volume specialization of the archive's integral-normalized formula. -/
def EuclideanGramFormula (n : ℕ) : Prop :=
  ∀ s : ℕ, 2 ≤ s → s + 2 ≤ n →
    let K := gramKernel s (((n : ℝ) - s - 1) / 2)
    gramLaw n s = (K univ)⁻¹ • K

theorem gramConstant_pos {n s : ℕ} (hn : s + 2 ≤ n) : 0 < gramConstant n s := by
  apply Finset.prod_pos
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have h : j + 1 < n := by omega
  have h' : (j : ℝ) + 1 < n := by exact_mod_cast h
  apply div_pos (Real.Gamma_pos_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) j])) (mul_pos
    (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith)))

theorem euclideanGramFormula_of_spherical {n : ℕ}
    (h : ∀ s, 2 ≤ s → s + 2 ≤ n → SphericalGramFormula n s) : EuclideanGramFormula n := by
  classical
  intro s hs hn
  let p := ((n : ℝ) - s - 1) / 2
  let C := ENNReal.ofReal (gramConstant n s)
  let K := gramKernel s p
  have hp : 0 < p := by
    have : (s : ℝ) + 2 ≤ n := by exact_mod_cast hn
    dsimp [p]
    linarith
  have hc := gramConstant_pos hn
  have he : gramLaw n s = C • K := by
    change gramLaw n s = C • (volume.restrict _).withDensity _
    rw [← withDensity_indicator (measurable_gramDomain s),
      ← withDensity_smul' C _ ENNReal.ofReal_ne_top]
    apply (h s hs hn).trans
    congr 1
    funext x
    by_cases hd : (correlation x).PosDef
    · simp [hd, Set.indicator_of_mem (show x ∈ gramDomain s from hd.posSemidef),
        C, ENNReal.ofReal_mul hc.le, p]
    · by_cases hsd : x ∈ gramDomain s
      · have hz : (correlation x).det = 0 := by
          by_contra hh
          exact hd ((show (correlation x).PosSemidef from hsd).posDef_iff_det_ne_zero.mpr hh)
        simp [hd, hsd, hz, Real.zero_rpow hp.ne']
      · simp [hd, hsd]
  let := uniform_probability (n := n) (by omega)
  have hm : gramLaw n s univ = 1 := by
    rw [gramLaw, Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [he, Measure.smul_apply, smul_eq_mul] at hm
  exact he.trans (congrArg (· • K) (ENNReal.eq_inv_of_mul_eq_one_left hm))

#print axioms gramConstant_pos
#print axioms euclideanGramFormula_of_spherical

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The v1 archive statement, using its PSD domain and determinant-integral normalizer. -/
def ClassicalGramFormula (μ : Measure E) : Prop :=
  ∀ s : ℕ, 2 ≤ s → s + 2 ≤ Module.finrank ℝ E →
    let K := gramKernel s (((Module.finrank ℝ E : ℝ) - s - 1) / 2)
    Measure.map (fun z : Fin s → Metric.sphere (0 : E) 1 ↦ fun ij : OffDiagonal s ↦
      inner ℝ (z ij.val.1 : E) (z ij.val.2 : E))
      (Measure.pi fun _ ↦ (μ.toSphere univ)⁻¹ • μ.toSphere) = (K univ)⁻¹ • K

open scoped Pointwise in
theorem classicalGramFormula_volume_of_spherical
    (h : ∀ s, 2 ≤ s → s + 2 ≤ Module.finrank ℝ E → SphericalGramFormula (Module.finrank ℝ E) s) :
    ClassicalGramFormula (volume : Measure E) := by
  let n := Module.finrank ℝ E
  let e := (stdOrthonormalBasis ℝ E).repr
  let M := Metric.sphere (0 : E) 1
  let f (x : M) : Sphere n := ⟨e x, mem_sphere_zero_iff_norm.mpr (by
    rw [e.norm_map]; exact mem_sphere_zero_iff_norm.mp x.property)⟩
  have hf : Measurable f :=
    (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable
  have pre (s : Set (Sphere n)) (hs : MeasurableSet s) :
      (volume : Measure E).toSphere (f ⁻¹' s) = (volume : Measure (Ambient n)).toSphere s := by
    rw [Measure.toSphere_apply' _ (hf hs), Measure.toSphere_apply' _ hs, e.finrank_eq]
    congr 1
    rw [← e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]
    congr 1
    ext z
    constructor
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨f w, hw, rfl⟩, (e.map_smul r w).symm⟩
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hz⟩
      let v : M := ⟨e.symm w, mem_sphere_zero_iff_norm.mpr (by
        rw [e.symm.norm_map]; exact mem_sphere_zero_iff_norm.mp w.property)⟩
      have hv : f v = w := Subtype.ext (e.apply_symm_apply _)
      exact ⟨r, hr, _, ⟨v, show f v ∈ s by rwa [hv], rfl⟩, e.injective (by simpa [v] using hz)⟩
  let μ := (volume : Measure E).toSphere
  have pres : MeasurePreserving f ((μ univ)⁻¹ • μ) (uniform n) := by
    refine ⟨hf, Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply hf hs, uniform, Measure.smul_apply, Measure.smul_apply]
    simp only [μ, pre s hs, show (volume : Measure E).toSphere univ = _ from
      (by simpa only [Set.preimage_univ] using pre univ MeasurableSet.univ)]
  intro s hs hn
  let := uniform_probability (n := n) (by dsimp [n]; omega)
  have hpi := measurePreserving_pi (fun _ : Fin s ↦ (μ univ)⁻¹ • μ)
    (fun _ ↦ uniform n) (fun _ ↦ pres)
  have ht := euclideanGramFormula_of_spherical h s hs hn
  apply Eq.trans _ ht
  rw [gramLaw, ← hpi.map_eq, Measure.map_map (by fun_prop) hpi.measurable]
  congr 1
  funext z ij
  exact (e.inner_map_map _ _).symm

#print axioms classicalGramFormula_volume_of_spherical

end Transport

end SigabaNeo.Rogers.Gram
