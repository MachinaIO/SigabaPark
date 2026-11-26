import Definitions.Def_LatticeAttack_Research_Wall1_HermiteSphereGram506
import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensSign506

set_option autoImplicit true

/-! Exact expansion of the degree-63 witness minus its constant mode in
kernels obtained by tangential differentiation on the 505-sphere. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506.Sphere

open Radial Finset Real
open scoped RealInnerProductSpace
private abbrev Poly := List ℚ
private def value (p : Poly) (x : ℝ) := eval (100*(x-(threshold:ℝ))) p
private def X : Poly := [threshold,1/100]
private def prod : Poly → Poly → Poly
  | [],_ => []
  | a::p,b => add (scale a b) (0 :: prod p b)

private theorem eval_prod (u : ℝ) (p q : Poly) : eval u (prod p q) = eval u p*eval u q := by
  induction p with
  | nil => simp [prod,eval]
  | cons a p ih => rw [prod,eval_add,eval_scale]; simp only [eval,Rat.cast_zero,zero_add,ih]; ring

private def derivCoeffs : Poly → Poly
  | [] | [_] => []
  | _::b::p => add (b::p) (0::derivCoeffs (b::p))

private theorem eval_deriv (u : ℝ) (p : Poly) :
    HasDerivAt (fun t ↦ eval t p) (eval u (derivCoeffs p)) u := by
  induction p with
  | nil => simpa only [eval,derivCoeffs] using hasDerivAt_const u (0:ℝ)
  | cons a p ih =>
    cases p with
    | nil => simpa [eval,derivCoeffs] using hasDerivAt_const u (a:ℝ)
    | cons b p =>
      have h := ((hasDerivAt_id u).mul ih).const_add (a:ℝ)
      simpa only [eval,derivCoeffs,eval_add,id_eq,Rat.cast_zero,zero_add,one_mul,Pi.mul_apply]
        using h

private def D (p : Poly) := scale 100 (derivCoeffs p)

private theorem value_deriv (p : Poly) (x : ℝ) : HasDerivAt (value p) (value (D p) x) x := by
  have h := (eval_deriv (100*(x-(threshold:ℝ))) p).comp x
    (((hasDerivAt_id x).sub_const (threshold:ℝ)).const_mul 100)
  apply h.congr_deriv
  simp only [value,D,eval_scale,Rat.cast_ofNat,mul_one]
  ring

private def up (α : ℚ) (p : Poly) :=
  let X2 := prod X X
  add (scale (α^2) (prod X p)) (add
    (prod (add [504+2*α] (scale (1-2*α) X2)) (D p))
    (prod (add (prod X X2) (scale (-1) X)) (D (D p))))

private theorem value_X (x : ℝ) : value X x = x := by simp [value,X,eval]; ring

private theorem up_gram {p : Poly} (h : Gram (value p)) (α : ℚ) : Gram (value (up α p)) := by
  have e : value (up α p) = fun x ↦ (α:ℝ)^2*x*value p x +
        (504+x^2+2*α*(1-x^2))*value (D p) x + (x^3-x)*value (D (D p)) x := by
    funext x
    have hx := value_X x
    unfold value at *
    simp only [up,eval_add,eval_scale,eval_prod,eval,Rat.cast_pow,
      Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_one,Rat.cast_neg,hx,mul_zero,add_zero]
    ring
  rw [e]
  exact raise_gram h (value_deriv p) (value_deriv (D p)) α

private def layers : ℕ → List (ℕ × Poly)
  | 0 => [(0,[1])]
  | j+1 =>
    let L := layers j
    (j+1, up (-((j:ℚ)+504)) (L.headD (0,[])).2)::L

private theorem layers_gram (n : ℕ) : ∀ k ∈ layers n, Gram (value k.2) := by
  induction n with
  | zero =>
    simp only [layers,List.mem_cons,List.not_mem_nil,or_false,forall_eq]
    rw [show value [1] = (fun _ ↦ (1:ℝ)) by funext x; simp [value,eval]]
    exact constant_gram
  | succ n ih =>
    intro k hk
    rcases List.mem_cons.mp hk with e | e
    · subst k
      apply up_gram
      apply ih
      cases n <;> simp [layers,List.headD]
    · exact ih k e

private def check : List (ℕ × Poly) → Poly → Bool
  | [],p => p.all (· == 0)
  | (n,g)::s,p =>
    let c := p[n]?.getD 0 / g[n]?.getD 0
    decide (0 ≤ c) && check s (add p (scale (-c) g))

private def target := add (scale (1/100) (0::prod factorCoeffs factorCoeffs)) [-fZero]

private theorem target_eval (x : ℝ) : value target x = sphericalKernel x - (fZero:ℝ) := by
  simp only [value,target,eval_add,eval_scale,eval,eval_prod,eval_factorCoeffs,Rat.cast_div,
    Rat.cast_zero,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat,zero_add,mul_zero,add_zero,sphericalKernel]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem expansion_checked : check (layers 63) target = true := by decide +kernel

private theorem eval_zero (p : Poly) (h : p.all (· == 0) = true) (x : ℝ) : value p x = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    obtain ⟨hc,hp⟩ := Bool.and_eq_true_iff.mp h
    have ec : c = 0 := eq_of_beq hc
    simp only [value,eval,ec,Rat.cast_zero,zero_add] at *
    rw [ih hp,mul_zero]

private theorem check_sound (s : List (ℕ × Poly)) (p : Poly)
    (good : ∀ k ∈ s, Gram (value k.2)) (cert : check s p = true)
    {ι : Type} (S : Finset ι) (u : ι → Space) (hu : ∀ i ∈ S, ‖u i‖ = 1) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, value p ⟪u i,u j⟫ := by
  induction s generalizing p with
  | nil => simp only [eval_zero p cert,Finset.sum_const_zero,le_rfl]
  | cons k s ih =>
    let c := p[k.1]?.getD 0 / k.2[k.1]?.getD 0
    obtain ⟨hc,hr⟩ := Bool.and_eq_true_iff.mp cert
    have hpos : (0:ℝ) ≤ c := by exact_mod_cast (of_decide_eq_true hc : 0 ≤ c)
    have hrem := ih (add p (scale (-c) k.2)) (fun a ha ↦ good a (List.mem_cons_of_mem _ ha)) hr
    have hg := gram_sum_nonneg (good k List.mem_cons_self) S u hu
    simp only [value,eval_add,eval_scale,Rat.cast_neg,neg_mul,←sub_eq_add_neg,
      Finset.sum_sub_distrib,← Finset.mul_sum] at hrem hg ⊢
    linarith [mul_nonneg hpos hg]

/-- The concrete spherical pair bound holds for all finite families, including repeated vectors. -/
theorem sphericalPairLower : SphericalPairLower := by
  intro ι S u hu
  have h := check_sound _ _ (layers_gram 63) expansion_checked S u hu
  simp only [target_eval,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at h
  nlinarith

/-- Physical rank-506 Hermite cap for every full discrete Euclidean lattice. -/
theorem shortest_cap (L : Submodule ℤ Space) [DiscreteTopology L] [IsZLattice ℝ L] {z : Space}
    (hz : DecoupledDecoder.IsShortest L z) :
    ‖z‖^2 ≤ 56.2142 * ZLattice.covolume L ^ (2/(506:ℝ)) :=
  shortest_cap_of_sphere_shell sphericalPairLower thinShellSign L hz

theorem laterDeterminantFloor : ControlledPlane.LaterDeterminantFloor :=
  laterFloor_of_spherical sphericalPairLower

end SigabaNeo.Wall1.HermiteWitness506.Sphere

#print axioms SigabaNeo.Wall1.HermiteWitness506.Sphere.sphericalPairLower
#print axioms SigabaNeo.Wall1.HermiteWitness506.Sphere.shortest_cap
#print axioms SigabaNeo.Wall1.HermiteWitness506.Sphere.laterDeterminantFloor
