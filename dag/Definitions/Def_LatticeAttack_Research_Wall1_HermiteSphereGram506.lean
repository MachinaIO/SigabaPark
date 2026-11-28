import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensMoments506

set_option autoImplicit true

/-! Tangential differentiation of finite Gram representations on the unit sphere. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506.Sphere

open Real Finset
open scoped RealInnerProductSpace ContDiff
set_option maxRecDepth 6000
set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 2400000

def Gram (p : ℝ → ℝ) : Prop := ∃ (ι : Type) (_ : Fintype ι) (F : ι → Space → ℝ),
  (∀ j, ContDiff ℝ ∞ (F j)) ∧ ∀ x y : Space, ‖x‖ = 1 → ‖y‖ = 1 →
    (∑ j, F j x * F j y) = p ⟪x,y⟫

theorem constant_gram : Gram (fun _ ↦ 1) :=
  ⟨Unit,inferInstance,fun _ _ ↦ 1,fun _ ↦ contDiff_const,by simp⟩

theorem gram_sum_nonneg {p : ℝ → ℝ} (g : Gram p) {ι : Type} (S : Finset ι)
    (u : ι → Space) (hu : ∀ i ∈ S, ‖u i‖ = 1) : 0 ≤ ∑ i ∈ S, ∑ j ∈ S, p ⟪u i,u j⟫ := by
  obtain ⟨κ,_,F,_,hF⟩ := g
  have eq : (∑ i ∈ S, ∑ j ∈ S, p ⟪u i,u j⟫) = ∑ k : κ, (∑ i ∈ S, F k (u i))^2 := by
    calc _ = ∑ i ∈ S, ∑ j ∈ S, ∑ k, F k (u i)*F k (u j) := by
               exact sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ (hF _ _ (hu i hi) (hu j hj)).symm
         _ = _ := by
               symm
               simp only [sq,sum_mul,mul_sum]
               rw [sum_comm (s:=univ) (t:=S)]
               apply sum_congr rfl; intro i _
               rw [sum_comm]
               simp only [mul_comm]
  exact eq ▸ sum_nonneg (fun _ _ ↦ sq_nonneg _)

private def axis (i : Fin 506) := EuclideanSpace.basisFun (Fin 506) ℝ i
private def tang (x : Space) (i : Fin 506) := axis i - (x i) • x

private theorem tang_inner (x y : Space) (i : Fin 506) :
    ⟪tang x i,y⟫ = y i - x i*⟪x,y⟫ := by simp only [tang,axis,inner_sub_left,real_inner_smul_left,EuclideanSpace.basisFun_inner]

private theorem curve (x : Space) (hx : ‖x‖=1) (i : Fin 506) :
    ∃ c : ℝ → Space, c 0 = x ∧ HasDerivAt c (tang x i) 0 ∧ ∀ t, ‖c t‖ = 1 := by
  let v := tang x i
  let h (t : ℝ) := t^2 * ‖v‖^2/4
  let c (t : ℝ) := (1+h t)⁻¹ • ((1-h t) • x + t • v)
  have h0 : h 0 = 0 := by simp [h]
  have hc : c 0 = x := by simp [c,h0]
  have dh : HasDerivAt h 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖v‖^2)).div_const 4 using 1 <;> norm_num [h]
  refine ⟨c,hc,?_,?_⟩
  · have d := ((dh.const_add 1).inv (by simp [h0])).smul
      (((dh.const_sub 1).smul_const x).add ((hasDerivAt_id (0:ℝ)).smul_const v))
    apply d.congr_deriv
    simp [h0,v,id_eq]
  · intro t
    have ht : 0 < 1+h t := by dsimp [h]; positivity
    have ortho : ⟪x,v⟫ = 0 := by
      rw [real_inner_comm,tang_inner,real_inner_self_eq_norm_sq,hx]; ring
    dsimp only [c]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),inv_mul_eq_iff_eq_mul₀ ht.ne',
      mul_one]
    apply (sq_eq_sq₀ (norm_nonneg _) ht.le).mp
    rw [norm_add_sq_real,norm_smul,norm_smul,real_inner_smul_left,real_inner_smul_right,
      ortho,hx,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs]
    dsimp [h]; ring

private def lift (α : ℝ) (i : Fin 506) (F : Space → ℝ) (x : Space) :=
  fderiv ℝ F x (tang x i) + α*x i*F x

private theorem lift_smooth {F : Space → ℝ} (h : ContDiff ℝ ∞ F) (α : ℝ) (i : Fin 506) :
    ContDiff ℝ ∞ (lift α i F) := by
  have df : ContDiff ℝ ∞ (fderiv ℝ F) := h.fderiv_right (by simp)
  unfold lift tang
  fun_prop

private theorem jet {ι : Type} [Fintype ι] (F : ι → Space → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (k : ι → ℝ) (α : ℝ) (x : Space) (i : Fin 506) (c : ℝ → Space)
    (hc : c 0 = x) (dc : HasDerivAt c (tang x i) 0) {g : ℝ → ℝ} {dg : ℝ}
    (eqn : ∀ t, (∑ j, k j * F j (c t)) = g t) (hg : HasDerivAt g dg 0) :
    (∑ j, k j * lift α i (F j) x) = dg + α*x i*g 0 := by
  have dj (j) := (((hF j).differentiable (by simp)).differentiableAt (x:=x)).hasFDerivAt
  have d (j) : HasDerivAt (fun t ↦ k j * F j (c t)) (k j * fderiv ℝ (F j) x (tang x i)) 0 := by
    have hx := dj j
    rw [← hc] at hx
    simpa only [hc,Function.comp_def] using (hx.comp_hasDerivAt 0 dc).const_mul (k j)
  have res := HasDerivAt.fun_sum (u:=univ) (fun j _ ↦ d j)
  have eq := funext eqn
  rw [eq] at res
  rw [hg.unique res,← eqn 0,hc]
  simp only [lift,mul_add,Finset.sum_add_distrib,mul_sum]
  congr 1
  apply sum_congr rfl; intro j _; ring

private theorem dot_sums (x y : Space) :
    ∑ i, x i * y i = ⟪x,y⟫ := by
  rw [real_inner_comm,PiLp.inner_apply]
  rfl

/-- Lifting each feature by a tangential derivative and an axial multiple
preserves a finite Gram representation. The trace term uses all 506 directions. -/
theorem raise_gram {p p' p'' : ℝ → ℝ} (g : Gram p)
    (der : ∀ t, HasDerivAt p (p' t) t) (der' : ∀ t, HasDerivAt p' (p'' t) t) (α : ℝ) :
    Gram (fun t ↦ α^2*t*p t + (504+t^2+2*α*(1-t^2))*p' t + (t^3-t)*p'' t) := by
  obtain ⟨ι,inst,F,hs,eq⟩ := g
  refine ⟨Fin 506 × ι,inferInstance,fun j ↦ lift α j.1 (F j.2),
    fun j ↦ lift_smooth (hs j.2) _ _,?_⟩
  intro x y hx hy
  let t := ⟪x,y⟫
  let A (i : Fin 506) := y i - x i*t
  let B (i : Fin 506) := x i - y i*t
  have first (i : Fin 506) (z : Space) (hz : ‖z‖=1) :
      (∑ j, lift α i (F j) x * F j z) =
        p' ⟪x,z⟫ * (z i - x i*⟪x,z⟫) + α*x i*p ⟪x,z⟫ := by
    obtain ⟨c,hc,dc,unit⟩ := curve x hx i
    have ip : HasDerivAt (fun w ↦ ⟪c w,z⟫) (z i - x i*⟪x,z⟫) 0 := by
      apply (dc.inner ℝ (hasDerivAt_const (0:ℝ) z)).congr_deriv
      simp only [inner_zero_right,zero_add,tang_inner]
    have hp := (der ⟪c 0,z⟫).comp 0 ip
    have j := jet F hs (fun j ↦ F j z) α x i c hc dc
      (g:=fun w ↦ p ⟪c w,z⟫) (dg:=p' ⟪x,z⟫ * (z i - x i*⟪x,z⟫)) (fun w ↦ by rw [← eq (c w) z (unit w) hz]; exact sum_congr rfl fun j _ ↦ mul_comm _ _)
      (by simpa only [Function.comp_def,tang_inner,hc,inner_zero_right,add_zero,zero_add] using hp)
    rw [← sum_congr rfl (fun (j : ι) (_ : j ∈ univ) ↦ mul_comm (F j z) (lift α i (F j) x))]
    simpa only [hc] using j
  have both (i : Fin 506) :
      (∑ j, lift α i (F j) x * lift α i (F j) y) =
      p'' t*B i*A i + p' t*(1-y i*y i-x i*B i) + α*x i*p' t*B i +
      α*y i*(p' t*A i+α*x i*p t) := by
    obtain ⟨c,hc,dc,unit⟩ := curve y hy i
    let h (w : ℝ) := ⟪x,c w⟫
    have h0 : h 0 = t := by simp only [h,hc,t]
    have dh : HasDerivAt h (B i) 0 := by
      apply ((hasDerivAt_const (0:ℝ) x).inner ℝ dc).congr_deriv
      simp only [inner_zero_left,add_zero]
      rw [real_inner_comm (tang y i) x,tang_inner,real_inner_comm x y]
    have di : HasDerivAt (fun w ↦ c w i) (1-y i*y i) 0 := by
      have H := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 506 ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt 0 dc
      apply H.congr_deriv
      change (tang y i) i = _
      simp [tang,axis,EuclideanSpace.basisFun_apply,PiLp.sub_apply,PiLp.smul_apply]
    have dp := (der (h 0)).comp 0 dh
    have dq := (der' (h 0)).comp 0 dh
    have d := (dq.mul (di.sub (dh.const_mul (x i)))).add (dp.const_mul (α*x i))
    have j := jet F hs (fun j ↦ lift α i (F j) x) α y i c hc dc
      (g:=fun w ↦ p' (h w)*(c w i-x i*h w)+α*x i*p (h w))
      (dg:=p'' t*B i*A i+p' t*(1-y i*y i-x i*B i)+α*x i*(p' t*B i))
      (fun w ↦ first i (c w) (unit w)) (by
        apply d.congr_deriv
        simp only [Function.comp_def,Pi.sub_apply,h0,hc,A])
    rw [j]
    simp only [h0,hc,A]
    ring
  have hxx : ∑ i, x i*x i = 1 := by rw [dot_sums,real_inner_self_eq_norm_sq,hx]; norm_num
  have hyy : ∑ i, y i*y i = 1 := by rw [dot_sums,real_inner_self_eq_norm_sq,hy]; norm_num
  have hxy : ∑ i, x i*y i = t := dot_sums ..
  rw [Fintype.sum_prod_type]
  simp_rw [both]
  have poly (i : Fin 506) :
      p'' t*B i*A i + p' t*(1-y i*y i-x i*B i) + α*x i*p' t*B i +
        α*y i*(p' t*A i+α*x i*p t) =
      p' t + (-p'' t*t - p' t + α*p' t)*(x i*x i+y i*y i) +
        (p'' t*(1+t^2)+p' t*t-2*α*p' t*t+α^2*p t)*(x i*y i) := by dsimp [A,B]; ring
  simp_rw [poly,Finset.sum_add_distrib,← mul_sum]
  simp only [Finset.sum_add_distrib,hxx,hyy,hxy,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp only [t]
  ring

end SigabaNeo.Wall1.HermiteWitness506.Sphere

#print axioms SigabaNeo.Wall1.HermiteWitness506.Sphere.raise_gram
