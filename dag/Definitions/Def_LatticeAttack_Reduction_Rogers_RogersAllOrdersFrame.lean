import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersCalibration
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped ENNReal
namespace SigabaNeo.Rogers.Frame

private theorem generic_extension {n k} (hk : 0 < k) (hn : k < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    ∀ᵐ y : E n ∂volume, ∀ᵐ x ∂frameMeasure D, LinearIndependent ℝ (Fin.cons y (x : FrameSpace n k)) := by
  let := frameMeasure_finiteOnCompacts hk hn hd hf
  apply (Measure.ae_ae_comm (p := fun (x : FrameSpace n k) (y : E n) ↦ LinearIndependent ℝ (Fin.cons y x))
    (isOpen_setOfPred_linearIndependent.preimage (continuous_snd.finCons continuous_fst)).measurableSet).mp
  filter_upwards [frameMeasure_ae_independent (k := k) D] with x hx
  have hlt : Submodule.span ℝ (range x) ≠ ⊤ := by
    intro h
    have hh := finrank_span_eq_card hx
    rw [h] at hh
    simp at hh
    omega
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume.addHaar_submodule _ hlt)] with y hy
  exact linearIndependent_finCons.mpr ⟨hx,hy⟩

private theorem axis_extension {n k} (hk : 0 < k) (hn : k < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (i : Fin n) : ∀ᵐ x ∂frameMeasure D,
      LinearIndependent ℝ (Fin.cons (EuclideanSpace.basisFun (Fin n) ℝ i) (x : FrameSpace n k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hi : ∀ᵐ y : E n ∂volume, y i ≠ 0 := by
    let f := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n ↦ ℝ) i).toLinearMap
    apply measure_eq_zero_iff_ae_notMem.mp (volume.addHaar_submodule (LinearMap.ker f) ?_)
    intro h
    have hb : b i ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simp [f,b,EuclideanSpace.basisFun_apply] at hb
  obtain ⟨y, hyi, hy⟩ := (hi.and (generic_extension hk hn hd hf)).exists
  let u (j : Fin n) := y j / y i
  let M : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix _ _ ℝ).updateCol i u
  have hM : M.det = 1 := by
    change (1 : Matrix (Fin n) (Fin n) ℝ).cramer u i = 1
    simp [Matrix.cramer_one,u,hyi]
  let g : SL n := ⟨M,hM⟩
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
    (g.toLin'.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm)
  have heb : e (b i) = (y i)⁻¹ • y := by
    apply WithLp.ofLp_injective 2
    change M.mulVec (WithLp.ofLp (b i)) = _
    rw [show WithLp.ofLp (b i) = Pi.single i 1 by
      ext j; simp [b, EuclideanSpace.basisFun_apply, Pi.single_apply]]
    ext l
    simp [M,Matrix.updateCol,u, div_eq_inv_mul]
  let A (x : FrameSpace n k) := fun a ↦ e (x a)
  have hm : Measurable A := Measurable.of_eval fun a ↦
    e.toLinearMap.continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply a)
  have ha : (frameMeasure D).map A = frameMeasure D := frameMeasure_sl_invariant hd g
  have hp : ∀ᵐ x ∂(frameMeasure D).map A, LinearIndependent ℝ (Fin.cons y x) := by rwa [ha]
  filter_upwards [ae_of_ae_map hm.aemeasurable hp] with x hx
  have hx' := linearIndependent_finCons.mp hx
  apply (e.linearIndependent_iff (LinearMap.ker_eq_bot.mpr e.injective)).mp
  change LinearIndependent ℝ (e ∘ Fin.cons (b i) x)
  rw [show e ∘ Fin.cons (b i) x = Fin.cons (e (b i)) (A x) by
    funext j; refine Fin.cases rfl (fun _ ↦ rfl) j]
  apply linearIndependent_finCons.mpr
  refine ⟨hx'.1, ?_⟩
  rw [heb]
  intro h
  exact hx'.2 (by simpa [smul_smul,hyi] using (Submodule.span ℝ (range (A x))).smul_mem (y i) h)

/-- Project the frame away from the target coordinate and solve the row equation using
the Gram matrix of the projected vectors. -/
theorem rogers_frame_measure (n k : ℕ) (hk : 0 < k) (hn : k < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    frameMeasure (k := k) D = groupHaar n D • Measure.pi (fun _ ↦ volume) := by
  classical
  obtain ⟨C,hC⟩ := frameMeasure_proportional_of_row hk hn hd hf (hle := by
    intro i v S
    let := frameMeasure_finiteOnCompacts hk hn hd hf
    let M (x : FrameSpace n k) : Matrix (Fin n) (Fin k) ℝ :=
      Matrix.of fun j a ↦ if j = i then 0 else x a j
    let G (x : FrameSpace n k) := (M x)ᵀ * M x
    let w (x : FrameSpace n k) := (G x).cramer v
    let p (j : Fin n) (x : FrameSpace n k) := ((M x).mulVec (w x)) j / (G x).det
    have cont (j a) : Continuous (fun x ↦ M x j a) := by
      dsimp [M]; split_ifs <;> fun_prop
    have cm : Continuous M := continuous_matrix cont
    have cg : Continuous G := cm.matrix_transpose.matrix_mul cm
    have cw : Continuous w := cg.matrix_cramer continuous_const
    apply row_translate_of_coefficients hd i v p _ _ _ S
    · intro j
      exact ((continuous_apply j).comp (cm.matrix_mulVec cw)).measurable.div
        cg.matrix_det.measurable
    · intro j x y he
      have eq : M x = M y := by
        ext j a
        dsimp [M]
        split_ifs with h
        · rfl
        · exact he a j h
      simp only [p,w,G,eq]
    · filter_upwards [axis_extension hk hn hd hf i] with x hx
      let y (a : Fin k) : E n := WithLp.toLp 2 fun j ↦ M x j a
      have hy : LinearIndependent ℝ y := by
        apply Fintype.linearIndependent_iff.mpr
        intro c hc a
        let d := -(∑ t, c t * x t i)
        apply Fintype.linearIndependent_iff.mp hx (Fin.cons d c) _ a.succ
        rw [Fin.sum_univ_succ]
        ext j
        by_cases hj : j = i
        · subst j
          simp [d,EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply]
        · have hh := congrArg (fun u : E n ↦ u j) hc
          simpa [y,M,hj, EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,
            WithLp.ofLp_sum] using hh
      have hG : G x = Matrix.gram ℝ y := by
        rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin n) ℝ)]
        rfl
      have hdet := (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hy : (Matrix.gram ℝ y).det ≠ 0)
      rw [← hG] at hdet
      intro a
      have hh := congrFun ((G x).mulVec_cramer v) a
      change ((M x)ᵀ * M x).mulVec (w x) a = (G x).det * v a at hh
      rw [← Matrix.mulVec_mulVec] at hh
      have hsum : ∑ j ∈ Finset.univ.erase i, (M x).mulVec (w x) j * x a j =
          (G x).det * v a := by
        rw [← hh]
        unfold Matrix.mulVec dotProduct
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp only [Matrix.transpose_apply, M, Matrix.of_apply, ite_true, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_right (Finset.mem_erase.mp hj).1, mul_comm]
      simp only [p, div_mul_eq_mul_div, ← Finset.sum_div, hsum]
      field_simp)
  exact frameMeasure_calibration n k hk hn D hd hf hC

#print axioms rogers_frame_measure
end SigabaNeo.Rogers.Frame
