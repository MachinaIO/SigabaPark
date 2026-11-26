import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

namespace FloodAux

open SigabaNeo.Lattices SigabaNeo.Lattices.Trapdoor.Family ZLattice ProbabilityTheory
  Cslib.Probability MeasureTheory
open scoped ENNReal Matrix

section
variable {n m q : ℕ} [NeZero q] (τ : ℝ) (hτ : 0 < τ)

noncomputable def rhoV (x : Fin m → ℤ) : ℝ := ∏ j, gw τ (x j)

noncomputable def gaussVec : PMF (Fin m → ℤ) :=
  (sampleList (gaussZ τ hτ) m).map (fun l (j : Fin m) => l.getD j default)

theorem gaussVec_apply (y : Fin m → ℤ) :
    gaussVec τ hτ y = ENNReal.ofReal (rhoV τ y) / ENNReal.ofReal (Mz τ) ^ m := by
  unfold gaussVec rhoV
  rw [vecLaw_apply]
  simp only [gaussZ_apply hτ, ENNReal.div_eq_inv_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]
  rw [ENNReal.ofReal_prod_of_nonneg (f := fun j => gw τ (y j))
    (fun j _ => (Real.exp_pos _).le)]

def castV (y : Fin m → ℤ) : Fin m → ZMod q := fun j => (y j : ZMod q)

variable (M : Matrix (Fin n) (Fin m) (ZMod q)) (d : (Fin n → ZMod q) → Fin m → ℤ)
  (hd : ∀ v, M *ᵥ castV (d v) = v)

def gsyn (u : Fin n → ZMod q) (y : Fin m → ℤ) : Fin m → ℤ := y + d (u - M *ᵥ castV y)

noncomputable def colLaw (u : Fin n → ZMod q) : PMF (Fin m → ℤ) :=
  (gaussVec τ hτ).map (gsyn M d u)

omit [NeZero q] in
theorem castV_add (a b : Fin m → ℤ) : (castV (a + b) : Fin m → ZMod q) = castV a + castV b := by
  funext j; simp [castV]

omit [NeZero q] in
theorem castV_sub (a b : Fin m → ℤ) : (castV (a - b) : Fin m → ZMod q) = castV a - castV b := by
  funext j; simp [castV]

include hd in
omit [NeZero q] in
theorem B_gsyn (u : Fin n → ZMod q) (y : Fin m → ℤ) : M *ᵥ castV (gsyn M d u y) = u := by
  unfold gsyn
  rw [castV_add, Matrix.mulVec_add, hd]
  abel

include hd in
omit [NeZero q] in
theorem gsyn_preimage (u : Fin n → ZMod q) (x : Fin m → ℤ) (hx : M *ᵥ castV x = u)
    (v : Fin n → ZMod q) : gsyn M d u (x - d v) = x := by
  unfold gsyn
  rw [castV_sub, Matrix.mulVec_sub, hd, hx, sub_sub_cancel, sub_add_cancel]

include hd in
theorem colLaw_apply (u : Fin n → ZMod q) (x : Fin m → ℤ) (hx : M *ᵥ castV x = u) :
    colLaw τ hτ M d u x = ∑ v : Fin n → ZMod q, gaussVec τ hτ (x - d v) := by
  classical
  have hinj : Function.Injective fun v : Fin n → ZMod q => x - d v := by
    intro v v' h
    have h' : d v = d v' := by simpa using h
    rw [← hd v, ← hd v', h']
  unfold colLaw
  rw [PMF.map_apply, tsum_eq_sum (s := Finset.univ.image fun v => x - d v)]
  · rw [Finset.sum_image fun a _ b _ h => hinj h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [if_pos (gsyn_preimage M d hd u x hx v).symm]
  · intro y hy
    rw [if_neg]
    intro h
    apply hy
    refine Finset.mem_image.mpr ⟨u - M *ᵥ castV y, Finset.mem_univ _, ?_⟩
    rw [h]; unfold gsyn; abel

include hd in
theorem colLaw_apply_off (u : Fin n → ZMod q) (x : Fin m → ℤ) (hx : M *ᵥ castV x ≠ u) :
    colLaw τ hτ M d u x = 0 :=
  map_apply_of_not_mem _ x fun y h => hx (h ▸ B_gsyn M d hd u y)

variable (b : ℕ)

noncomputable def Rr : ℝ := τ * m

def Box : Set (Fin m → ℤ) := {x | ∀ j, |((x j : ℤ) : ℝ)| < Rr (m := m) τ}

noncomputable def θT : ℝ := Real.pi * m * ((b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b) / τ ^ 2

theorem rhoV_eq (x : Fin m → ℤ) :
    rhoV τ x = Real.exp (-Real.pi * (∑ j, ((x j : ℤ) : ℝ) ^ 2) / τ ^ 2) := by
  unfold rhoV gw
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]

theorem rhoV_eq_weight (x : Fin m → ℤ) : rhoV τ x = gaussianWeight τ (embed m x) := by
  rw [rhoV_eq]
  unfold gaussianWeight
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [embed]

theorem shift_bound (x e : Fin m → ℤ) (hx : x ∈ Box τ) (he : ∀ j, |e j| ≤ b) :
    |∑ j, ((((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)| ≤
      m * ((b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j, |(((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2| ≤
      (b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b := by
    intro j
    have h1 : |((e j : ℤ) : ℝ)| ≤ b := by exact_mod_cast he j
    have h2 := (hx j).le
    have : (((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2 =
        ((e j : ℤ) : ℝ) ^ 2 - 2 * ((x j : ℤ) : ℝ) * ((e j : ℤ) : ℝ) := by
      simp only [Pi.sub_apply, Int.cast_sub]; ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_mul, abs_mul, abs_two]
    have h0 : 0 ≤ |((e j : ℤ) : ℝ)| := abs_nonneg _
    have h0' : 0 ≤ |((x j : ℤ) : ℝ)| := abs_nonneg _
    nlinarith
  calc ∑ j, |(((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2|
      ≤ ∑ _j : Fin m, ((b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b) := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by simp; ring

include hτ in
theorem rho_shift_ge (x e : Fin m → ℤ) (hx : x ∈ Box τ) (he : ∀ j, |e j| ≤ b) :
    Real.exp (-θT (m := m) τ b) * rhoV τ x ≤ rhoV τ (x - e) := by
  rw [rhoV_eq, rhoV_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := abs_le.mp (shift_bound τ b x e hx he)
  have hτ2 : 0 < τ ^ 2 := by positivity
  set A := ∑ j, ((x j : ℤ) : ℝ) ^ 2
  set D := ∑ j, ((((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)
  have hsum : ∑ j, ((((x - e) j : ℤ) : ℝ) ^ 2) = A + D := by
    simp only [A, D, Finset.sum_sub_distrib]; ring
  rw [hsum]
  have e' : -θT (m := m) τ b + -Real.pi * A / τ ^ 2 =
      -Real.pi * (A + m * ((b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b)) / τ ^ 2 := by
    unfold θT; field_simp; ring
  rw [e']
  apply div_le_div_of_nonneg_right _ hτ2.le
  nlinarith [Real.pi_pos, h.2]

include hτ in
theorem rho_shift_le (x e : Fin m → ℤ) (hx : x ∈ Box τ) (he : ∀ j, |e j| ≤ b) :
    rhoV τ (x - e) ≤ Real.exp (θT (m := m) τ b) * rhoV τ x := by
  rw [rhoV_eq, rhoV_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := abs_le.mp (shift_bound τ b x e hx he)
  have hτ2 : 0 < τ ^ 2 := by positivity
  set A := ∑ j, ((x j : ℤ) : ℝ) ^ 2
  set D := ∑ j, ((((x - e) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)
  have hsum : ∑ j, ((((x - e) j : ℤ) : ℝ) ^ 2) = A + D := by
    simp only [A, D, Finset.sum_sub_distrib]; ring
  rw [hsum]
  have e' : θT (m := m) τ b + -Real.pi * A / τ ^ 2 =
      -Real.pi * (A - m * ((b : ℝ) ^ 2 + 2 * Rr (m := m) τ * b)) / τ ^ 2 := by
    unfold θT; field_simp; ring
  rw [e']
  apply div_le_div_of_nonneg_right _ hτ2.le
  nlinarith [Real.pi_pos, h.1]

theorem gaussVec_tail (hτ1 : 1 ≤ τ) :
    (gaussVec (m := m) τ hτ).toOuterMeasure {y | ∃ j, τ * Real.sqrt m ≤ |((y j : ℤ) : ℝ)|} ≤
      (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) := by
  rw [toOuterMeasure_eq_ev]
  unfold gaussVec
  rw [ev_map]
  refine (ev_mono _ fun l => ind_mono (Q := ∃ x ∈ l, τ * Real.sqrt m ≤ |((x : ℤ) : ℝ)|) ?_).trans
    (ev_sampleList_exists _ _ ?_ m)
  · rintro ⟨j, hj⟩
    simp only [Set.mem_ofPred_eq, List.getD_eq_getElem?_getD] at hj
    cases hx : l[(j : ℕ)]? with
    | none =>
      rw [hx] at hj; simp at hj
      have : 0 < τ * Real.sqrt m := mul_pos hτ (Real.sqrt_pos.mpr (by
        have := j.pos; exact_mod_cast this))
      linarith
    | some x => rw [hx] at hj; exact ⟨x, List.mem_of_getElem? hx, hj⟩
  · exact (toOuterMeasure_eq_ev (gaussZ τ hτ)
      {x : ℤ | τ * Real.sqrt m ≤ |(x : ℝ)|}).symm.le.trans (gaussZ_tail hτ1 hτ m)

theorem colLaw_tail (hτ1 : 1 ≤ τ) (hb : ∀ v j, |d v j| ≤ b)
    (hrad : τ * Real.sqrt m + b ≤ Rr (m := m) τ) (u : Fin n → ZMod q) :
    (colLaw τ hτ M d u).toOuterMeasure (Box τ)ᶜ ≤
      (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) := by
  unfold colLaw
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (measure_mono ?_) (gaussVec_tail τ hτ hτ1)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_compl_iff, Box, Set.mem_ofPred_eq, not_forall,
    not_lt] at hy
  obtain ⟨j, hj⟩ := hy
  refine ⟨j, ?_⟩
  have hd' : |((d (u - M *ᵥ castV y) j : ℤ) : ℝ)| ≤ b := by exact_mod_cast hb _ j
  have hsum : ((gsyn M d u y j : ℤ) : ℝ) =
      ((y j : ℤ) : ℝ) + ((d (u - M *ᵥ castV y) j : ℤ) : ℝ) := by
    simp [gsyn]
  rw [hsum] at hj
  have := abs_add_le ((y j : ℤ) : ℝ) ((d (u - M *ᵥ castV y) j : ℤ) : ℝ)
  linarith

theorem coset_box_tail (u : Fin n → ZMod q) (hB : dualMassE M τ ≤ 1 / 2)
    {p : PMF (Fin m → ℤ)} (hp : cosetGauss M u τ hτ = some p) :
    p.toOuterMeasure (Box τ)ᶜ ≤ ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2)) := by
  refine le_trans (measure_mono ?_) (cosetGauss_tail_M _ u hτ hB hp (m ^ 2))
  intro x hx
  simp only [Set.mem_compl_iff, Box, Set.mem_ofPred_eq, not_forall, not_lt] at hx
  obtain ⟨j, hj⟩ := hx
  simp only [Set.mem_ofPred_eq]
  have : τ * Real.sqrt ((m ^ 2 : ℕ) : ℝ) = Rr (m := m) τ := by
    unfold Rr; push_cast; rw [Real.sqrt_sq (by positivity)]
  rw [this]
  exact hj.trans (abs_le_norm_embed x j)

include hd in
/-- **The flooding column law is close to the coset Gaussian.** -/
theorem colLaw_close (hτ1 : 1 ≤ τ) (hb : ∀ v j, |d v j| ≤ b)
    (hrad : τ * Real.sqrt m + b ≤ Rr (m := m) τ)
    (u : Fin n → ZMod q) (hB : dualMassE M τ ≤ 1 / 2)
    {p : PMF (Fin m → ℤ)} (hp : cosetGauss M u τ hτ = some p) :
    CloseTo (colLaw τ hτ M d u) p
      (ENNReal.ofReal (2 * θT (m := m) τ b) + (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) +
        ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2))) := by
  classical
  obtain ⟨Mm, hM, hpx⟩ := cosetGauss_apply _ u hτ hp
  set C : Set (Fin m → ℤ) := {x | M *ᵥ castV x = u}
  set Z := ENNReal.ofReal (Mz τ) ^ m
  set Mc := ENNReal.ofReal Mm
  set Qn : ℝ≥0∞ := (Fintype.card (Fin n → ZMod q) : ℝ≥0∞)
  set c := Qn * Mc / Z
  set tg := (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m)
  set θ := θT (m := m) τ b
  set P := colLaw τ hτ M d u
  have hMc0 : Mc ≠ 0 := (ENNReal.ofReal_pos.mpr hM).ne'
  have hMct : Mc ≠ ⊤ := ENNReal.ofReal_ne_top
  -- masses on the coset
  have hp_on : ∀ x ∈ C, p x = ENNReal.ofReal (rhoV τ x) / Mc := by
    intro x hx
    rw [hpx, if_pos (show (M *ᵥ fun i => ((x i : ℤ) : ZMod q)) = u from hx), rhoV_eq_weight]
  have hp_off : ∀ x ∉ C, p x = 0 := by
    intro x hx; rw [hpx, if_neg (show ¬ (M *ᵥ fun i => ((x i : ℤ) : ZMod q)) = u from hx)]
  have hcp : ∀ x ∈ C, c * p x = Qn * ENNReal.ofReal (rhoV τ x) / Z := by
    intro x hx
    rw [hp_on x hx]
    simp only [c, div_eq_mul_inv]
    calc Qn * Mc * Z⁻¹ * (ENNReal.ofReal (rhoV τ x) * Mc⁻¹)
        = Qn * ENNReal.ofReal (rhoV τ x) * Z⁻¹ * (Mc * Mc⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hMc0 hMct, mul_one]
  have hP_on : ∀ x ∈ C, P x = (∑ v : Fin n → ZMod q,
      ENNReal.ofReal (rhoV τ (x - d v))) / Z := by
    intro x hx
    rw [colLaw_apply τ hτ M d hd u x hx]
    simp only [gaussVec_apply, ENNReal.div_eq_inv_mul, ← Finset.mul_sum]
    rfl
  have hlow : ∀ x ∈ Box τ, x ∈ C → ENNReal.ofReal (Real.exp (-θ)) * (c * p x) ≤ P x := by
    intro x hbx hx
    rw [hcp x hx, hP_on x hx]
    simp only [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (Real.exp (-θ)) * (Z⁻¹ * (Qn * ENNReal.ofReal (rhoV τ x)))
        = Z⁻¹ * ∑ _v : Fin n → ZMod q, ENNReal.ofReal (Real.exp (-θ) * rhoV τ x) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ _ := by
          gcongr with v
          exact rho_shift_ge τ hτ b x _ hbx (hb v)
  have hup : ∀ x ∈ Box τ, x ∈ C → P x ≤ ENNReal.ofReal (Real.exp θ) * (c * p x) := by
    intro x hbx hx
    rw [hcp x hx, hP_on x hx]
    simp only [ENNReal.div_eq_inv_mul]
    calc Z⁻¹ * ∑ v : Fin n → ZMod q, ENNReal.ofReal (rhoV τ (x - d v))
        ≤ Z⁻¹ * ∑ _v : Fin n → ZMod q, ENNReal.ofReal (Real.exp θ * rhoV τ x) := by
          gcongr with v
          exact rho_shift_le τ hτ b x _ hbx (hb v)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
  -- `c` from the tails
  have hPC : P.toOuterMeasure Cᶜ = 0 := by
    rw [PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x ∈ Cᶜ
    · rw [Set.indicator_of_mem hx]; exact colLaw_apply_off τ hτ M d hd u x hx
    · rw [Set.indicator_of_notMem hx]
  have hPbox : P.toOuterMeasure (Box τ ∩ C) ≤ ENNReal.ofReal (Real.exp θ) * c := by
    rw [PMF.toOuterMeasure_apply]
    calc ∑' x, (Box τ ∩ C).indicator P x ≤ ∑' x, ENNReal.ofReal (Real.exp θ) * c * p x := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : x ∈ Box τ ∩ C
          · rw [Set.indicator_of_mem hx, mul_assoc]; exact hup x hx.1 hx.2
          · rw [Set.indicator_of_notMem hx]; exact zero_le
      _ = ENNReal.ofReal (Real.exp θ) * c := by rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]
  have h1 : 1 ≤ ENNReal.ofReal (Real.exp θ) * c + tg := by
    have hsplit : (1 : ℝ≥0∞) ≤ P.toOuterMeasure (Box τ ∩ C) + P.toOuterMeasure (Box τ)ᶜ := by
      calc (1 : ℝ≥0∞) = P.toOuterMeasure Set.univ := by
            rw [eq_comm, PMF.toOuterMeasure_apply_eq_one_iff]; intro x _; trivial
        _ ≤ P.toOuterMeasure ((Box τ ∩ C) ∪ ((Box τ)ᶜ ∪ Cᶜ)) := measure_mono fun x _ => by
            by_cases h1 : x ∈ Box τ <;> by_cases h2 : x ∈ C
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr (Or.inr h2)
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inl h1)
        _ ≤ P.toOuterMeasure (Box τ ∩ C) + (P.toOuterMeasure (Box τ)ᶜ + P.toOuterMeasure Cᶜ) :=
            (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
        _ = _ := by rw [hPC, add_zero]
    calc (1 : ℝ≥0∞) ≤ P.toOuterMeasure (Box τ ∩ C) + P.toOuterMeasure (Box τ)ᶜ := hsplit
      _ ≤ _ := add_le_add hPbox (colLaw_tail τ hτ M d b hτ1 hb hrad u)
  have hc : 1 - tg ≤ ENNReal.ofReal (Real.exp θ) * c := tsub_le_iff_right.mpr h1
  -- the domination
  set a := ENNReal.ofReal (Real.exp (-(2 * θ))) * (1 - tg)
  have hdom : ∀ x ∈ Box τ, a * p x ≤ P x := by
    intro x hbx
    by_cases hx : x ∈ C
    · calc a * p x = ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp (-θ)) *
            (1 - tg) * p x := by
            simp only [a]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
        _ ≤ ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp (-θ)) *
            (ENNReal.ofReal (Real.exp θ) * c) * p x := by gcongr
        _ = ENNReal.ofReal (Real.exp (-θ)) * (c * p x) := by
            have : ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ) = 1 := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
                Real.exp_zero, ENNReal.ofReal_one]
            calc _ = (ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ)) *
                ENNReal.ofReal (Real.exp (-θ)) * (c * p x) := by ring
              _ = _ := by rw [this, one_mul]
        _ ≤ P x := hlow x hbx hx
    · rw [hp_off x hx, mul_zero]; exact zero_le
  refine (closeTo_of_ge P p (Box τ) hdom).mono ?_
  have hθ : 0 ≤ θ := by
    simp only [θ, θT, Rr]; positivity
  have hs1 : ENNReal.ofReal (Real.exp (-(2 * θ))) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have h1s : 1 - ENNReal.ofReal (Real.exp (-(2 * θ))) ≤ ENNReal.ofReal (2 * θ) := by
    rw [tsub_le_iff_right, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.add_one_le_exp (-(2 * θ))]
  calc 1 - a + p.toOuterMeasure (Box τ)ᶜ
      ≤ (1 - ENNReal.ofReal (Real.exp (-(2 * θ))) + tg) +
        ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2)) := by
        gcongr
        · exact one_sub_mul_le _ _ hs1
        · exact coset_box_tail τ hτ M u hB hp
    _ ≤ _ := by gcongr

include hd in
/-- **Flooding preimages of a matrix target are close to `Trapdoor.preimage`.** -/
theorem preimage_close {k : ℕ} (hτ1 : 1 ≤ τ) (hb : ∀ v j, |d v j| ≤ b)
    (hrad : τ * Real.sqrt m + b ≤ Rr (m := m) τ) (hB : dualMassE M τ ≤ 1 / 2)
    (P : Matrix (Fin n) (Fin k) (ZMod q)) :
    CloseTo ((sampleOptList ((List.finRange k).map fun c =>
        some (colLaw τ hτ M d (fun i => P i c)))).map
          (Option.map fun cols r j => (cols.getD j.val 0) r))
      (Trapdoor.preimage M P τ hτ)
      (k * (ENNReal.ofReal (2 * θT (m := m) τ b) + (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) +
        ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2)))) := by
  unfold Trapdoor.preimage
  refine CloseTo.map ?_ _
  have h := closeTo_sampleOptList
    (ε := ENNReal.ofReal (2 * θT (m := m) τ b) + (m : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m) +
        ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ (m ^ 2)))
    (ds := (List.finRange k).map fun c => colLaw τ hτ M d (fun i => P i c))
    (es := (List.finRange k).map fun c => cosetGauss M (fun i => P i c) τ hτ) (by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun c _ => ?_
      have hs : (cosetGauss M (fun i => P i c) τ hτ).isSome :=
        (cosetGauss_isSome_iff M _ τ hτ).mpr ⟨d (fun i => P i c), hd _⟩
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨p, hp, colLaw_close τ hτ M d hd b hτ1 hb hrad _ hB hp⟩)
  rw [List.map_map, List.length_map, List.length_finRange] at h
  exact h

end

end FloodAux


namespace FloodAux
open Matrix AdvancedEncryption.WE.Assumptions.SuccinctLWE SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

/-- A preimage map for `W` padded with zeros is one for `[I_ℓ ⊗ B | W]`. -/
theorem stacked_mulVec_pad {n m ℓ q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (x : Fin m → ℤ) :
    stacked B W *ᵥ (fun j : Fin (ℓ * m + m) =>
        (((if h : j.val < ℓ * m then (0 : ℤ) else x ⟨j.val - ℓ * m, by omega⟩) : ℤ) : ZMod q)) =
      W *ᵥ fun j => ((x j : ℤ) : ZMod q) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt, ↓reduceDIte, Int.cast_zero, mul_zero,
    Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ¬ ((Fin.natAdd (ℓ * m) j).val < ℓ * m) := by simp
  have e : (⟨ℓ * m + j.val - ℓ * m, by omega⟩ : Fin m) = j := Fin.ext (by simp)
  have e' : (⟨(Fin.natAdd (ℓ * m) j).val - ℓ * m, by simp⟩ : Fin m) = j := Fin.ext (by simp)
  have h2 : ¬ (ℓ * m + j.val < ℓ * m) := by omega
  simp only [stacked, h, ↓reduceDIte, e, e', h2]


/-- **The encryptor's succinct-LWE trapdoor without a trapdoor for `B`.** Each column of `T` is the
flooding sample `y + [0; d_W(t − M y)]`, `y ← D_{Z^{ℓm+m}, σ}`, `M = [I_ℓ ⊗ B | W]`, `t` the
column of `I_ℓ ⊗ G`, where `d_W` is any short preimage map of `W` alone. If `Λ^⊥(M)` is smooth
at `σ`, this law is within `ℓ n k · (2θ + 6 M 4^{−M} + 3 · 2^M 4^{−M²})` of the assumption's
`trapdoorLaw`, with `M = ℓ m + m` and `θ = π M (b² + 2 σ M b) / σ²`. -/
theorem trapdoorLaw_flood_close (p : Params) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (dW : (Fin (p.ℓ * p.n) → ZMod p.q) → Fin p.m → ℤ)
    (hdW : ∀ v, W *ᵥ (fun j => ((dW v j : ℤ) : ZMod p.q)) = v) (b : ℕ)
    (hb : ∀ v j, |dW v j| ≤ b)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + b ≤ (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ))
    (hB : dualMassE (stacked B W) p.σ ≤ 1 / 2) :
    CloseTo
      ((sampleOptList ((List.finRange (p.ℓ * (p.n * p.k))).map fun c =>
          some (((sampleList (gaussZ (p.σ : ℝ) hσ) (p.ℓ * p.m + p.m)).map
              (fun l (j : Fin (p.ℓ * p.m + p.m)) => l.getD j default)).map fun y =>
            y + fun j : Fin (p.ℓ * p.m + p.m) =>
              if h : j.val < p.ℓ * p.m then (0 : ℤ) else
                dW ((fun i => blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i c) -
                  stacked B W *ᵥ fun j => ((y j : ℤ) : ZMod p.q))
                  ⟨j.val - p.ℓ * p.m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) j.isLt⟩))).map
        (Option.map fun cols r j => (cols.getD j.val 0) r))
      (trapdoorLaw p B W)
      ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          ((b : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) * b) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2)))) := by
  have hpos : 0 < p.σ := by exact_mod_cast hσ
  have hlaw : trapdoorLaw p B W = Trapdoor.preimage (stacked B W)
      (blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q)) p.σ hσ := by
    unfold trapdoorLaw; rw [dif_pos hpos]
  rw [hlaw]
  let d : (Fin (p.ℓ * p.n) → ZMod p.q) → Fin (p.ℓ * p.m + p.m) → ℤ := fun v j =>
    if h : j.val < p.ℓ * p.m then (0 : ℤ) else dW v ⟨j.val - p.ℓ * p.m, by omega⟩
  have hd : ∀ v, stacked B W *ᵥ castV (d v) = v := fun v => by
    have h := stacked_mulVec_pad B W (dW v)
    rw [hdW] at h
    exact h
  have hbd : ∀ v j, |d v j| ≤ b := fun v j => by
    simp only [d]; split_ifs
    · simp
    · exact hb v _
  exact preimage_close (p.σ : ℝ) hσ (stacked B W) d hd b hσ1 hbd (by simpa [Rr] using hrad) hB _

end FloodAux

theorem solution (p : Params) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (dW : (Fin (p.ℓ * p.n) → ZMod p.q) → Fin p.m → ℤ)
    (hdW : ∀ v, W *ᵥ (fun j => ((dW v j : ℤ) : ZMod p.q)) = v) (b : ℕ)
    (hb : ∀ v j, |dW v j| ≤ b)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + b ≤ (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ))
    (hB : dualMassE (stacked B W) p.σ ≤ 1 / 2) :
    CloseTo
      ((sampleOptList ((List.finRange (p.ℓ * (p.n * p.k))).map fun c =>
          some (((sampleList (gaussZ (p.σ : ℝ) hσ) (p.ℓ * p.m + p.m)).map
              (fun l (j : Fin (p.ℓ * p.m + p.m)) => l.getD j default)).map fun y =>
            y + fun j : Fin (p.ℓ * p.m + p.m) =>
              if h : j.val < p.ℓ * p.m then (0 : ℤ) else
                dW ((fun i => blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i c) -
                  stacked B W *ᵥ fun j => ((y j : ℤ) : ZMod p.q))
                  ⟨j.val - p.ℓ * p.m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) j.isLt⟩))).map
        (Option.map fun cols r j => (cols.getD j.val 0) r))
      (trapdoorLaw p B W)
      ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          ((b : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) * b) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2)))) :=
  FloodAux.trapdoorLaw_flood_close p hσ hσ1 B W dW hdW b hb hrad hB
