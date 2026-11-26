module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_GramDensity

set_option autoImplicit true

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace SigabaNeo.Rogers.Gram

def densityLaw (n s : ℕ) : Measure (OffDiagonal s → ℝ) :=
  volume.withDensity fun x ↦ ENNReal.ofReal (gramDensity n x)

theorem spherical_iff_densityLaw (n s : ℕ) :
    SphericalGramFormula n s ↔ gramLaw n s = densityLaw n s := by
  classical
  unfold SphericalGramFormula gramLaw densityLaw gramDensity
  simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]

theorem gramDensity_eq_zero_outside {s : ℕ} (n : ℕ) (a : Fin s → ℝ)
    (y : OffDiagonal s → ℝ) (i : Fin s) (hi : a i ∉ Ioo (-1) 1) :
    gramDensity n ((splitGram s).symm (a,y)) = 0 := by
  classical
  apply if_neg
  intro h
  let e : Fin 2 → Fin (s+1) := ![0, i.succ]
  have he : Function.Injective e := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [e, Ne.symm (Fin.succ_ne_zero i)]
  have hd := (h.submatrix he).det_pos
  rw [Matrix.det_fin_two] at hd
  simp [e, Matrix.submatrix_apply, correlation] at hd
  change a i * a i < 1 at hd
  apply hi
  exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp (by nlinarith))

theorem gramLaw_one (n : ℕ) (hn : 0 < n) : gramLaw n 1 = densityLaw n 1 := by
  classical
  letI : IsEmpty (OffDiagonal 1) := ⟨fun ⟨⟨i,j⟩,h⟩ ↦ (not_lt_of_ge (Subsingleton.elim i j).ge) h⟩
  have hc (x : OffDiagonal 1 → ℝ) : correlation x = 1 := by
    ext i j
    have := Subsingleton.elim i j
    subst j
    simp [correlation]
  have hd (x : OffDiagonal 1 → ℝ) : gramDensity n x = 1 := by
    simp [gramDensity, hc, Matrix.PosDef.one, gramConstant]
  letI := uniform_probability hn
  have hprob : IsProbabilityMeasure (gramLaw n 1) :=
    by
      unfold gramLaw
      apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2
      infer_instance
  unfold densityLaw
  simp only [hd, ENNReal.ofReal_one, withDensity_one]
  apply Measure.ext
  intro s _
  induction s using Subsingleton.set_cases <;> simp [volume_pi, Measure.pi_univ]

def DensityRecursion (m s : ℕ) : Prop :=
  ∀ (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞), Measurable F →
    (∫⁻ x, F (splitGram s x) ∂densityLaw (m+1) (s+1)) =
    ∫⁻ a : Fin s → ℝ, ∫⁻ x, F (a, fun ij ↦ angularThird (a ij.val.1) (a ij.val.2) (x ij))
      ∂densityLaw m s ∂Measure.pi (fun _ ↦ volume.withDensity (weight (((m:ℝ)+1-3)/2)))

theorem spherical_of_density_recursion
    (step : ∀ m s, 1 ≤ s → s + 2 ≤ m → DensityRecursion m s) :
    ∀ n s : ℕ, 2 ≤ s → s + 2 ≤ n → SphericalGramFormula n s := by
  suffices h : ∀ k n, k+1+2 ≤ n → gramLaw n (k+1) = densityLaw n (k+1) by
    rintro n (_|s) hs hn
    · omega
    exact (spherical_iff_densityLaw ..).2 (h s n hn)
  intro k
  induction k with
  | zero => exact fun n hn ↦ gramLaw_one n (by omega)
  | succ k ih =>
    rintro (_|m) hn
    · omega
    apply Measure.ext_of_lintegral
    intro f hf
    let F := f ∘ (splitGram (k+1)).symm
    have hF : Measurable F := hf.comp (splitGram _).symm.measurable
    have h := gramLaw_recursion (m := m) (by omega) F hF
    rw [ih m (by omega), ← step m (k+1) (by omega) (by omega) F hF] at h
    simpa [F] using h

#print axioms spherical_of_density_recursion
end SigabaNeo.Rogers.Gram
