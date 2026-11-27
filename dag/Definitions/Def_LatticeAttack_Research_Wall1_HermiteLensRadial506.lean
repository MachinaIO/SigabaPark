import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLens506

set_option autoImplicit true

/-! A rational polynomial enclosure and a signed quadrature certificate on the
log-radial interval [0,5]. The change of variables uses U = 100 (x - threshold). -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506.Radial

open Real Finset TerminalProjection.TerminalInterval

def add : List ℚ → List ℚ → List ℚ
  | [],b => b
  | a,[] => a
  | a::s,b::t => (a+b)::add s t

def scale (c : ℚ) (p : List ℚ) := p.map (c*·)

def eval (u : ℝ) : List ℚ → ℝ
  | [] => 0
  | a::s => a + u*eval u s

theorem eval_add (u : ℝ) (p q : List ℚ) :
    eval u (add p q) = eval u p + eval u q := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih => cases q <;> simp [add,eval,ih]
                   ring

theorem eval_scale (u : ℝ) (c : ℚ) (p : List ℚ) :
    eval u (scale c p) = c * eval u p := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,Rat.cast_mul] at *; rw [ih]; ring

/-- Coefficients in U of the Gegenbauer recurrence at threshold + U/100. -/
private def shifted : ℕ → List ℚ × List ℚ
  | 0 => ([1],[threshold,1/100])
  | j+1 =>
    let (a,b) := shifted j
    let k : ℚ := j+1
    (b,add (scale ((2*k+504)/(k+504))
      (add (scale threshold b) (0::scale (1/100) b))) (scale (-k/(k+504)) a))

private theorem eval_shift (u : ℝ) (j : ℕ) :
    (eval u (shifted j).1,eval u (shifted j).2) = zonalPair ((threshold:ℝ)+u/100) j := by
  induction j with
  | zero => norm_num [shifted,zonalPair,eval]; ring
  | succ j ih =>
    have a := congrArg Prod.fst ih
    have b := congrArg Prod.snd ih
    dsimp only at a b
    simp only [shifted,zonalPair,eval_add,eval_scale,eval,Rat.cast_zero,zero_add,
      Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_neg,Rat.cast_one,
      Rat.cast_ofNat,a,b]
    congr 1
    ring

private def coeff : ℕ → List ℚ
  | 0 => []
  | j+1 => add (coeff j) (scale (q j) (shifted j).1)

private theorem eval_coeff (u : ℝ) (n : ℕ) :
    eval u (coeff n) = ∑ j ∈ range n, (q j : ℝ) * (zonalPair ((threshold:ℝ)+u/100) j).1 := by
  induction n with
  | zero => simp [coeff,eval]
  | succ n ih =>
    rw [coeff,eval_add,eval_scale,ih,sum_range_succ]
    rw [show eval u (shifted n).1 = _ from congrArg Prod.fst (eval_shift u n)]

/-- Taylor coefficients of the spherical factor in U = 100 (x - threshold). -/
def factorCoeffs := coeff 32

theorem eval_factorCoeffs (x : ℝ) :
    eval (100*(x-(threshold:ℝ))) factorCoeffs = sphericalFactor x := by
  rw [factorCoeffs,eval_coeff,show (threshold:ℝ)+100*(x-threshold)/100=x by ring]
  rfl

private def denom := ((coeff 32).headD 0)
private def approx : List ℚ :=
  [1,1.267532,0.740915,0.267787,0.067582,0.012736,0.001870,0.000220,0.000021]
private def remainder := add (scale denom⁻¹ (coeff 32)) (scale (-1) approx)
private def size (p : List ℚ) := (p.map abs).sum

private theorem eval_abs (u : ℝ) (hu : |u| ≤ 1) (p : List ℚ) : |eval u p| ≤ (size p : ℝ) := by
  induction p with
  | nil => simp [eval,size]
  | cons c p ih =>
    simp only [eval,size,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_abs] at *
    apply (abs_add_le ((c:ℚ):ℝ) (u*eval u p)).trans
    apply add_le_add_right
    rw [abs_mul]
    exact (mul_le_mul hu ih (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

private theorem denom_pos : 0 < denom := by decide +kernel
private theorem error_cert : size remainder ≤ 0.00001 := by decide +kernel

private theorem approx_bound {u : ℝ} (hu : |u| ≤ 1) :
    |sphericalFactor ((threshold:ℝ)+u/100)/(denom:ℝ) - eval u approx| ≤ 0.00001 := by
  have h := (eval_abs u hu remainder).trans ((Rat.cast_le (K:=ℝ)).2 error_cert)
  simp only [remainder,eval_add,eval_scale,eval_coeff,Rat.cast_neg,Rat.cast_one,
    Rat.cast_inv,neg_one_mul,← sub_eq_add_neg] at h
  simpa only [sphericalFactor,div_eq_inv_mul,Rat.cast_ofScientific] using h

private structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

private def Box.holds (b : Box) (x : ℝ) := (b.lo:ℝ) ≤ x ∧ x ≤ (b.hi:ℝ)
private def singleton (c : ℚ) : Box := ⟨c,c⟩
private def plus (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
private def times (a b : Box) : Box :=
  let p := a.lo*b.lo
  let q := a.lo*b.hi
  let r := a.hi*b.lo
  let s := a.hi*b.hi
  ⟨min (min p q) (min r s), max (max p q) (max r s)⟩

private theorem plus_holds {a b : Box} {x y : ℝ} (ha : a.holds x) (hb : b.holds y) :
    (plus a b).holds (x+y) := by
  simpa only [Box.holds,plus,Rat.cast_add] using And.intro
    (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

private theorem times_holds {a b : Box} {x y : ℝ} (ha : a.holds x) (hb : b.holds y) :
    (times a b).holds (x*y) := by
  rcases ha with ⟨ha,ha'⟩
  rcases hb with ⟨hb,hb'⟩
  simp only [Box.holds,times,Rat.cast_min,Rat.cast_max,Rat.cast_mul,min_le_iff,le_max_iff]
  constructor
  · by_cases hy : 0 ≤ y
    · have h := mul_le_mul_of_nonneg_right ha hy
      by_cases hp : 0 ≤ (a.lo:ℝ)
      · exact .inl (.inl ((mul_le_mul_of_nonneg_left hb hp).trans h))
      · exact .inl (.inr ((mul_le_mul_of_nonpos_left hb' (le_of_not_ge hp)).trans h))
    · have h := mul_le_mul_of_nonpos_right ha' (le_of_not_ge hy)
      by_cases hp : 0 ≤ (a.hi:ℝ)
      · exact .inr (.inl ((mul_le_mul_of_nonneg_left hb hp).trans h))
      · exact .inr (.inr ((mul_le_mul_of_nonpos_left hb' (le_of_not_ge hp)).trans h))
  · by_cases hy : 0 ≤ y
    · have h := mul_le_mul_of_nonneg_right ha' hy
      by_cases hp : 0 ≤ (a.hi:ℝ)
      · exact .inr (.inr (h.trans (mul_le_mul_of_nonneg_left hb' hp)))
      · exact .inr (.inl (h.trans (mul_le_mul_of_nonpos_left hb (le_of_not_ge hp))))
    · have h := mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)
      by_cases hp : 0 ≤ (a.lo:ℝ)
      · exact .inl (.inr (h.trans (mul_le_mul_of_nonneg_left hb' hp)))
      · exact .inl (.inl (h.trans (mul_le_mul_of_nonpos_left hb (le_of_not_ge hp))))

private def horner (u : Box) : List ℚ → Box
  | [] => singleton 0
  | c::s => plus (singleton c) (times u (horner u s))

private theorem horner_holds {u : Box} {x : ℝ} (hx : u.holds x) (p : List ℚ) :
    (horner u p).holds (eval x p) := by
  induction p with
  | nil => exact ⟨by norm_num [horner,singleton,eval],by norm_num [horner,singleton,eval]⟩
  | cons c p ih => exact plus_holds ⟨le_rfl,le_rfl⟩ (times_holds hx ih)

/-- Axis-slice enclosure of 100 times the angular excess on bin j. -/
private def bin (j : ℕ) : Box :=
  ⟨0.1108768 - 100*0.836951*(j+1)/(32*505), 0.1108769 - 100*0.827693*j/(32*505)⟩

private def binUpper (j : ℕ) : ℚ :=
  let u := bin j
  let p := plus (horner u approx) ⟨-0.00001,0.00001⟩
  (times u (times p p)).hi

theorem kernel_on_bin (j : Fin 160) {x : ℝ}
    (hlo : (0.1108768:ℝ) - 100*0.836951*(j.val+1)/(32*505) ≤ 100*(x-(threshold:ℝ)))
    (hhi : 100*(x-(threshold:ℝ)) ≤ 0.1108769 - 100*0.827693*j.val/(32*505)) :
    100 * sphericalKernel x / (denom:ℝ)^2 ≤ binUpper j.val := by
  let u := 100*(x-(threshold:ℝ))
  have h : (bin j.val).holds u := by
    simpa only [bin,Box.holds,Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat,
      Rat.cast_ofScientific,Rat.cast_one,Rat.cast_natCast,u] using And.intro hlo hhi
  have hj : (j.val:ℝ) ≤ 159 := by exact_mod_cast (show j.val ≤ 159 by omega)
  have hu : |u| ≤ 1 := abs_le.mpr ⟨by dsimp [u]; linarith,by dsimp [u]; linarith [Nat.cast_nonneg (α:=ℝ) j.val]⟩
  have ap := approx_bound hu
  rw [show (threshold:ℝ)+u/100 = x by dsimp [u]; ring,abs_le] at ap
  have rem : (⟨-0.00001,0.00001⟩ : Box).holds
      (sphericalFactor x/(denom:ℝ)-eval u approx) := by
    simpa [Box.holds] using ap
  have hp := plus_holds (horner_holds h approx) rem
  rw [add_sub_cancel] at hp
  have hh := (times_holds h (times_holds hp hp)).2
  calc _ = u * ((sphericalFactor x / (denom:ℝ)) * (sphericalFactor x / (denom:ℝ))) := by
             unfold sphericalKernel u; ring
       _ ≤ _ := hh

private def ratio : Box := ⟨0.96923323,0.96923324⟩
private def weighted : ℕ → Box
  | 0 => singleton 0
  | n+1 => plus (singleton (binUpper (160-(n+1)))) (times ratio (weighted n))

private theorem ratio_holds : ratio.holds (exp (-1/32)) := by
  have lo := exp_lower (1/32) (1/0.96923324) (by decide +kernel) (by decide +kernel)
  have hi := exp_upper (1/32) (1/0.96923323) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Box.holds,ratio,Rat.cast_ofScientific]
  rw [show (-1/32:ℝ) = -(1/32) by ring,exp_neg,inv_eq_one_div]
  push_cast at lo hi
  constructor
  · apply (le_div_iff₀ (exp_pos _)).mpr
    linarith
  · apply (div_le_iff₀ (exp_pos _)).mpr
    linarith

private theorem signed_cert : (weighted 160).hi < 0 := by decide +kernel

/-- Strictly negative sum of the whole-bin upper bounds, with their geometric
exponential weights. The common positive factor 1-exp(-1/32) is omitted. -/
theorem signed_bin_sum :
    (∑ j ∈ range 160, exp (-1/32:ℝ)^j * (binUpper j:ℝ)) < 0 := by
  let r := exp (-1/32:ℝ)
  have go (n : ℕ) (hn : n ≤ 160) : (weighted n).holds
      (∑ j ∈ range n, r^j * (binUpper (160-n+j):ℝ)) := by
    induction n with
    | zero => simp [weighted,singleton,Box.holds]
    | succ n ih =>
      rw [sum_range_succ']
      simp only [pow_zero,one_mul,add_zero,pow_succ']
      have eq (k : ℕ) : 160-(n+1)+(k+1) = 160-n+k := by omega
      simp only [eq,mul_assoc,← mul_sum]
      rw [add_comm (r * _) ((binUpper _ : ℚ):ℝ)]
      exact plus_holds (a:=singleton (binUpper (160-(n+1)))) ⟨le_rfl,le_rfl⟩
        (times_holds ratio_holds (ih (by omega)))
  have h := (go 160 le_rfl).2.trans_lt ((Rat.cast_lt (K:=ℝ)).2 signed_cert)
  simpa [r] using h


open MeasureTheory in
/-- Integral sign on the first five log-radial units. Only the two affine
bounds on the physical angular profile are needed throughout this interval. -/
theorem integral_profile_neg (x : ℝ → ℝ) (hx : ContinuousOn x (Set.Icc 0 5))
    (lower : ∀ w ∈ Set.Icc (0:ℝ) 5,
      0.1108768 - 100*0.836951*w/505 ≤ 100*(x w-(threshold:ℝ)))
    (upper : ∀ w ∈ Set.Icc (0:ℝ) 5,
      100*(x w-(threshold:ℝ)) ≤ 0.1108769 - 100*0.827693*w/505) :
    (∫ w in (0:ℝ)..5, exp (-w) * sphericalKernel (x w)) < 0 := by
  let a (j : ℕ) : ℝ := j/32
  let r := exp (-1/32:ℝ)
  let c : ℝ := (denom:ℝ)^2/100
  have hc : 0 < c := by dsimp [c]; positivity [show (0:ℝ) < denom by exact_mod_cast denom_pos]
  have hr : r < 1 := exp_lt_one_iff.mpr (by norm_num)
  have ord (j) : a j ≤ a (j+1) := by dsimp [a]; push_cast; linarith
  let f (w : ℝ) := exp (-w) * sphericalKernel (x w)
  have inc {j : ℕ} (hj : j < 160) : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc 0 5 := by
    intro w h
    have hj' : (j:ℝ) ≤ 159 := by exact_mod_cast (show j ≤ 159 by omega)
    obtain ⟨h₁,h₂⟩ := h
    dsimp [a] at h₁ h₂
    push_cast at h₂
    exact ⟨by linarith [Nat.cast_nonneg (α:=ℝ) j],by linarith⟩
  have integ (j) (hj : j < 160) : IntervalIntegrable f volume (a j) (a (j+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (ord j)]
    exact (continuous_exp.comp continuous_neg).continuousOn.mul
      (kernel_continuous.comp_continuousOn (hx.mono (inc hj)))
  have er (j : ℕ) : exp (-(a j)) = r^j := by
    rw [show -(a j) = (j:ℝ)*(-1/32) by dsimp [a]; ring,exp_nat_mul]
  have each (j : ℕ) (hj : j ∈ range 160) : (∫ w in a j..a (j+1), f w) ≤
      (c*(1-r)) * (r^j*(binUpper j:ℝ)) := by
    have hj' := mem_range.mp hj
    let C : ℝ := c*(binUpper j:ℝ)
    calc _ ≤ ∫ w in a j..a (j+1), exp (-w)*C := by
                apply intervalIntegral.integral_mono_on (ord j) (integ j hj')
                  (((continuous_exp.comp continuous_neg).mul continuous_const).intervalIntegrable ..)
                intro w hw
                apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
                have h₁ := lower w (inc hj' hw)
                have h₂ := upper w (inc hj' hw)
                have l := hw.1
                have h := hw.2
                dsimp [a] at l h
                push_cast at h
                have hh := kernel_on_bin ⟨j,hj'⟩ (x:=x w) (by dsimp; linarith) (by dsimp; linarith)
                have hp : 0 < (denom:ℝ)^2 := pow_pos (by exact_mod_cast denom_pos) _
                have := (div_le_iff₀ hp).mp hh
                dsimp [C,c]
                linarith
         _ = _ := by
               rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_comp_neg,integral_exp,
                 er,er,pow_succ]
               dsimp only [C]; ring
  have hsum := (sum_le_sum each).trans_lt (show
      (∑ j ∈ range 160, (c*(1-r))*(r^j*(binUpper j:ℝ))) < 0 by
    rw [← mul_sum]; exact mul_neg_of_pos_of_neg (mul_pos hc (sub_pos.mpr hr)) signed_bin_sum)
  rw [intervalIntegral.sum_integral_adjacent_intervals integ] at hsum
  simpa only [a,Nat.cast_zero,zero_div,show ((160:ℕ):ℝ)/32 = 5 by norm_num] using hsum

end SigabaNeo.Wall1.HermiteWitness506.Radial

#print axioms SigabaNeo.Wall1.HermiteWitness506.Radial.kernel_on_bin
#print axioms SigabaNeo.Wall1.HermiteWitness506.Radial.signed_bin_sum

#print axioms SigabaNeo.Wall1.HermiteWitness506.Radial.integral_profile_neg
