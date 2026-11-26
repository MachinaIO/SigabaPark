module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelOrbitEvaluation

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev ContentFiber (n c : ℕ) := {z : NonzeroIntVector n // vectorContent z = c}

theorem vectorContent_ne_zero {n : ℕ} (z : NonzeroIntVector n) : vectorContent z ≠ 0 := by
  intro h
  apply z.property
  funext i
  simpa using (Finset.gcd_eq_zero_iff.mp h i (Finset.mem_univ i))

theorem scaledContent {n c : ℕ} (v : Fin n → ℤ) :
    (Finset.univ.gcd fun i ↦ ((c : ℤ) * v i).natAbs) =
      c * Finset.univ.gcd (fun i ↦ (v i).natAbs) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Finset.gcd_mul_left, normalize_eq]

def scalePrimitive {n c : ℕ} (hc : c ≠ 0) (v : ContentFiber n 1) : ContentFiber n c := by
  let w := fun i ↦ (c : ℤ) * v.val.val i
  have hw : w ≠ 0 := by
    intro h
    apply v.val.property
    funext i
    have := congrFun h i
    simpa [w, hc] using this
  refine ⟨⟨w, hw⟩, ?_⟩
  change (Finset.univ.gcd fun i ↦ (w i).natAbs) = c
  rw [show Finset.univ.gcd (fun i ↦ (w i).natAbs) =
    c * vectorContent v.val from scaledContent _, v.property, mul_one]

theorem scalePrimitive_bijective {n c : ℕ} (hc : c ≠ 0) :
    Function.Bijective (scalePrimitive (n := n) hc) := by
  constructor
  · intro v w h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have he := congrArg (fun z : ContentFiber n c ↦ z.val.val i) h
    simpa [scalePrimitive, hc] using he
  · intro z
    have hd (i : Fin n) : (c : ℤ) ∣ z.val.val i := by
      apply Int.natCast_dvd.mpr
      exact dvd_trans (dvd_of_eq z.property.symm) (Finset.gcd_dvd (Finset.mem_univ i))
    choose v hv using hd
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact z.val.property (funext fun i ↦ by simpa using hv i)
    have he : vectorContent z.val = c * vectorContent ⟨v, hv0⟩ := by
      change Finset.univ.gcd _ = _
      simpa only [hv, vectorContent] using scaledContent (c := c) v
    have hone : vectorContent ⟨v, hv0⟩ = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc)
      simpa [← he] using z.property
    exact ⟨⟨⟨v, hv0⟩, hone⟩, Subtype.ext (Subtype.ext (funext fun i ↦ (hv i).symm))⟩

/-- Reindex the full domain integral by positive dilations of primitive vectors. -/
theorem siegel_integral_by_primitive {n : ℕ} (D : Set (SL n)) (f : E n → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) =
      ∑' k : ℕ, ∑' v : ContentFiber n 1,
        vectorOrbitalIntegral D (fun x ↦ f (((k + 1 : ℕ) : ℝ) • x)) v.val := by
  let a := fun c ↦ ∑' z : ContentFiber n c, vectorOrbitalIntegral D f z.val
  rw [siegel_integral_by_content D f hf]
  change ∑' c, a c = _
  refine (tsum_eq_zero_add' (CompleteLattice.summable (f := fun k ↦ a (k + 1)))).trans ?_
  dsimp only [a]
  have : IsEmpty (ContentFiber n 0) := ⟨fun v ↦ vectorContent_ne_zero v.val v.property⟩
  rw [tsum_empty, zero_add]
  apply tsum_congr
  intro k
  let e := Equiv.ofBijective _ (scalePrimitive_bijective (n := n) (Nat.succ_ne_zero k))
  rw [← e.tsum_eq (fun z ↦ vectorOrbitalIntegral D f z.val)]
  apply tsum_congr
  intro v
  apply lintegral_congr
  intro g
  apply congrArg f
  apply WithLp.ofLp_injective 2
  change g.val.mulVec (fun j ↦ (((k + 1 : ℕ) : ℤ) * v.val.val j : ℤ)) =
    ((k + 1 : ℕ) : ℝ) • g.val.mulVec (fun j ↦ (v.val.val j : ℝ))
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  push_cast
  rfl

/-- The Jacobian of the positive dilation indexed by `k` in the primitive-vector sum. -/
def dilationWeight (n k : ℕ) : ℝ≥0∞ := ENNReal.ofReal |(((k + 1 : ℕ) : ℝ) ^ n)⁻¹|

theorem lintegral_dilation {n : ℕ} (k : ℕ) (f : E n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : E n, f (((k + 1 : ℕ) : ℝ) • x)) = dilationWeight n k * ∫⁻ x, f x := by
  have h : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← lintegral_map hf (measurable_const_smul _), Measure.map_addHaar_smul volume h,
    lintegral_smul_measure]
  simp only [dilationWeight, finrank_euclideanSpace_fin, smul_eq_mul]

theorem siegel_of_primitive_constant {n : ℕ} (D : Set (SL n)) (C : ℝ≥0∞)
    (prim : ∀ (u : E n → ℝ≥0∞), Measurable u →
      ∑' v : ContentFiber n 1, vectorOrbitalIntegral D u v.val = C * ∫⁻ x, u x)
    (mass : C * ∑' k, dilationWeight n k = groupHaar n D)
    (f : E n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) = groupHaar n D * ∫⁻ x, f x := by
  rw [siegel_integral_by_primitive D f hf]
  calc
    _ = ∑' k : ℕ, (C * dilationWeight n k) * ∫⁻ x, f x := by
      apply tsum_congr
      intro k
      rw [prim (fun x ↦ f (((k + 1 : ℕ) : ℝ) • x)) (hf.comp (measurable_const_smul _)), lintegral_dilation k f hf, mul_assoc]
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, mass]

#print axioms siegel_of_primitive_constant

end SigabaNeo.Rogers
