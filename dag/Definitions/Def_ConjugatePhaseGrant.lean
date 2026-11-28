import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic
namespace ConjugatePhaseGrant
open Cslib.Probability
variable {F W X S : Type} [Field F] [AddCommGroup W] [Module F W] [AddCommGroup X] [Module F X]

/-- The issuer publishes the restriction of its random functional to generator columns and one scalar. -/
def packet (L : W →ₗ[F] X) (δ : X) (phase : F) (k : Module.Dual F X) :=
  (k.comp L,phase+k δ)

theorem opens (L : W →ₗ[F] X) (δ : X) (w : W) (hw : L w=δ)
    (phase : F) (k : Module.Dual F X) :
    (packet L δ phase k).2-(packet L δ phase k).1 w=phase := by simp [packet,hw]

/-- A separation certificate exists for *every* unreachable difference. -/
theorem separator (L : W →ₗ[F] X) {δ : X} (h : δ ∉ LinearMap.range L) :
    ∃ k : Module.Dual F X,k.comp L=0 ∧ k δ=1 := by
  let p := LinearMap.range L
  obtain ⟨u,hu⟩ := Module.Projective.exists_dual_eq_one F
    (show p.mkQ δ≠0 by simpa [p,Submodule.mkQ_apply] using h)
  refine ⟨u.comp p.mkQ,?_,hu⟩
  ext w
  have hz : p.mkQ (L w)=0 := (Submodule.Quotient.mk_eq_zero p).2 ⟨w,rfl⟩
  simp [hz]

variable [Fintype (Module.Dual F X)]
noncomputable def law (L : W →ₗ[F] X) (δ : X) (phase : F) :=
  (Cslib.Probability.PMF.uniformOfFintype (Module.Dual F X)).map (packet L δ phase)

theorem blind (L : W →ₗ[F] X) {δ : X} (h : δ ∉ LinearMap.range L) (phase : F) :
    law L δ phase=law L δ 0 := by
  obtain ⟨v,hv,hd⟩ := separator L h
  let shift := Equiv.addLeft (phase • v)
  have he := congrArg (PMF.map (packet L δ 0))
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv shift)
  rw [PMF.map_comp] at he
  refine Eq.trans ?_ he
  apply congrArg (fun f ↦ (Cslib.Probability.PMF.uniformOfFintype (Module.Dual F X)).map f)
  funext k; apply Prod.ext
  · ext w
    have hz := LinearMap.congr_fun hv w
    change v (L w)=0 at hz
    simp [packet,shift,Function.comp_def,hz]
  · simp [packet,shift,Function.comp_def,hd]

theorem joint {Ω H : Type} (μ : PMF Ω) (front : Ω → H) (phase : Ω → F)
    (L : W →ₗ[F] X) {δ : X} (h : δ ∉ LinearMap.range L) :
    μ.bind (fun ω ↦ (law L δ (phase ω)).map fun a ↦ (front ω,a)) =
    μ.bind (fun ω ↦ (law L δ 0).map fun a ↦ (front ω,a)) := by simp only [blind L h]

/-- Nonlinear relabellings preserve the affine transporter language. -/
def move (e : S ≃ X) (L : W →ₗ[F] X) (x : S) (w : W) : S := e.symm (e x+L w)
theorem accepts (e : S ≃ X) (L : W →ₗ[F] X) (x y : S) (w : W) :
    move e L x w=y ↔ L w=e y-e x := by
  rw [move,Equiv.symm_apply_eq,eq_sub_iff_add_eq']
theorem no_iff (e : S ≃ X) (L : W →ₗ[F] X) (x y : S) :
    (¬∃ w,move e L x w=y) ↔ e y-e x ∉ LinearMap.range L := by
  simp only [accepts,LinearMap.mem_range]
/-- Computable nonlinear relabelling for any public function, including a fixed NAND evaluator. -/
def shear (f : X → F) : X × F ≃ X × F where
  toFun p := (p.1,p.2+f p.1)
  invFun p := (p.1,p.2-f p.1)
  left_inv p := by simp
  right_inv p := by simp

theorem shear_step (f : X → F) (a : X) (b : F) (w : X) :
    move (shear f) (LinearMap.inl F X F) (a,b) w =
      (a+w,b+f a-f (a+w)) := by simp [move,shear,LinearMap.inl_apply]
/-- Independent route packets can all carry the same actual challenge phase. -/
theorem shared {ι Ω H : Type} [Fintype ι] [Finite (Module.Dual F W × F)]
    (μ : PMF Ω) (front : Ω → H) (phase : Ω → F)
    (L : ι → W →ₗ[F] X) (δ : ι → X) (no : ∀ i,δ i ∉ LinearMap.range (L i)) :
    μ.bind (fun ω ↦ (Cslib.Probability.PMF.pi (fun i ↦ law (L i) (δ i) (phase ω))).map
      fun a ↦ (front ω,a)) =
    μ.bind (fun ω ↦ (Cslib.Probability.PMF.pi (fun i ↦ law (L i) (δ i) 0)).map
      fun a ↦ (front ω,a)) := by
  have eq (ω : Ω) : (fun i ↦ law (L i) (δ i) (phase ω)) = (fun i ↦ law (L i) (δ i) 0) :=
    funext fun i ↦ blind (L i) (no i) (phase ω)
  simp only [eq]
end ConjugatePhaseGrant
