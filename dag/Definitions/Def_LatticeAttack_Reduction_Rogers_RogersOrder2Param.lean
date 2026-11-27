import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Siegel

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev LineIndex (n : ℕ) := Σ q : ℕ, Σ _ : Diagram 1 2 (q+1), NonzeroIntVector n

private theorem pivot_zero {q} (A : Diagram 1 2 (q+1)) : A.pivot 0 = 0 :=
  Fin.ext (A.first 0 rfl)

private theorem line_first {q} (A : Diagram 1 2 (q+1)) : A.entry 0 0 = (q+1 : ℕ) := by
  simpa [pivot_zero] using A.pivotColumn 0 0

private theorem line_ne {q} (A : Diagram 1 2 (q+1)) (j : Fin 2) : A.entry 0 j ≠ 0 := by
  obtain ⟨i, h⟩ := A.nonzeroColumn j
  simpa only [Subsingleton.elim i 0] using h

private theorem line_coprime {q} (A : Diagram 1 2 (q+1)) :
    IsCoprime (A.entry 0 1) ((q+1 : ℕ) : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  apply A.primitive
  intro i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  fin_cases j
  · change _ ∣ A.entry 0 0
    rw [line_first A]; exact Int.gcd_dvd_right _ _
  · exact Int.gcd_dvd_left _ _

private def lineRat {q} (A : Diagram 1 2 (q+1)) : ℚ :=
  ⟨A.entry 0 1, q+1, by omega, Int.isCoprime_iff_gcd_eq_one.mp (line_coprime A)⟩

private def ratDiagram (q : ℕ) (b : ℤ) (hb : b ≠ 0) (hc : IsCoprime b ((q+1 : ℕ) : ℤ)) :
    Diagram 1 2 (q+1) where
  entry _ := ![(q+1 : ℕ), b]
  pivot _ := 0
  increasing := Subsingleton.strictMono _
  first := by simp
  nonzeroColumn j := by refine ⟨0, ?_⟩; fin_cases j <;> simp [hb]; omega
  pivotColumn := by intro i a; simp [Subsingleton.elim i a]
  echelon := by simp
  primitive := by
    intro d hd
    have h := hc.isUnit_of_dvd' (hd 0 1) (hd 0 0)
    simpa using Int.isUnit_iff_natAbs_eq.mp h

def lineIntegerPair {n : ℕ} (t : LineIndex n) : OrderTwoPair n :=
  fun j ↦ ⟨fun i ↦ t.2.1.entry 0 j * t.2.2.val i, by
    intro h
    exact t.2.2.property (funext fun i ↦
      (mul_eq_zero.mp (congrFun h i)).resolve_left (line_ne _ _))⟩

private theorem pair_dependent {n} (t : LineIndex n) :
    lineIntegerPair t ∈ (orderTwoIndependent n)ᶜ := by
  intro h
  have H := Fintype.linearIndependent_iff.mp h ![t.2.1.entry 0 1, -t.2.1.entry 0 0]
  apply line_ne t.2.1 1 (H ?_ 0)
  funext i
  simp [Fin.sum_univ_two, lineIntegerPair]
  ring

def linePairMap {n} (t : LineIndex n) : ↥((orderTwoIndependent n)ᶜ) :=
  ⟨lineIntegerPair t, pair_dependent t⟩

private theorem linePair_injective {n} : Function.Injective (linePairMap (n := n)) := by
  rintro ⟨q,A,x⟩ ⟨s,B,y⟩ h
  have he (i : Fin 2) (j : Fin n) : A.entry 0 i * x.val j = B.entry 0 i * y.val j :=
    congrArg (fun z : ↥((orderTwoIndependent n)ᶜ) ↦ (z.val i).val j) h
  obtain ⟨j,hj⟩ : ∃ j, x.val j ≠ 0 := by
    by_contra! H; exact x.property (funext H)
  have h0 := he 0 j
  rw [line_first, line_first] at h0
  have h1 := he 1 j
  have hc : A.entry 0 1 * ((s+1 : ℕ) : ℤ) = B.entry 0 1 * ((q+1 : ℕ) : ℤ) := by
    apply mul_right_cancel₀ hj
    linear_combination ((s+1 : ℕ) : ℤ) * h1 - B.entry 0 1 * h0
  have hr : lineRat A = lineRat B := by
    rw [← (lineRat A).num_div_den, ← (lineRat B).num_div_den, div_eq_div_iff] <;>
      first | exact_mod_cast hc | positivity
  have hq : q+1 = s+1 := congrArg Rat.den hr
  obtain rfl : q = s := by omega
  have hb : A.entry 0 1 = B.entry 0 1 := congrArg Rat.num hr
  have hp : A.pivot = B.pivot := funext fun i ↦ by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [pivot_zero,pivot_zero]
  have ha : A.entry = B.entry := by
    funext i k
    obtain rfl : i = 0 := Subsingleton.elim _ _
    fin_cases k
    · exact (line_first A).trans (line_first B).symm
    · exact hb
  have hab : A = B := by cases A; cases B; congr
  subst B
  have hxy : x = y := Subtype.ext (funext fun i ↦ mul_left_cancel₀ (line_ne A 0) (he 0 i))
  subst y
  rfl

private theorem linePair_surjective {n} : Function.Surjective (linePairMap (n := n)) := by
  rintro ⟨z,hz⟩
  change ¬LinearIndependent ℤ (fun i ↦ (z i).val) at hz
  rw [Fintype.linearIndependent_iff] at hz
  push Not at hz
  obtain ⟨c, hc, i, hi⟩ := hz
  have rel (j : Fin n) : c 0 * (z 0).val j + c 1 * (z 1).val j = 0 := by
    simpa [Fin.sum_univ_two] using congrFun hc j
  have hboth (i : Fin 2) (h : c i = 0) : c = 0 := by
    have aux (a : ℤ) (v : NonzeroIntVector n) (h : ∀ j, a * v.val j = 0) : a = 0 := by
      by_contra ha
      exact v.property (funext fun j ↦ (mul_eq_zero.mp (h j)).resolve_left ha)
    funext k
    fin_cases i <;> fin_cases k
    · exact h
    · exact aux _ (z 1) (fun j ↦ by simpa [show c 0 = 0 from h] using rel j)
    · exact aux _ (z 0) (fun j ↦ by simpa [show c 1 = 0 from h] using rel j)
    · exact h
  have hn (k : Fin 2) : c k ≠ 0 := fun h ↦ hi (congrFun (hboth k h) i)
  let r : ℚ := -(c 0 : ℚ) / (c 1 : ℚ)
  have hr : r ≠ 0 := div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hn 0))
    (by exact_mod_cast hn 1)
  have rr (j : Fin n) : (r.den : ℤ) * (z 1).val j = r.num * (z 0).val j := by
    have ht : ((z 1).val j : ℚ) = r * ((z 0).val j : ℚ) := by
      dsimp [r]
      field_simp [show (c 1 : ℚ) ≠ 0 by exact_mod_cast hn 1]
      have ht : (c 0 : ℚ) * ((z 0).val j : ℚ) + (c 1 : ℚ) * ((z 1).val j : ℚ) = 0 := by
        exact_mod_cast rel j
      linarith
    have hden : (r.den : ℚ) ≠ 0 := by positivity
    have hrat := (div_eq_iff hden).mp r.num_div_den
    exact_mod_cast (show (r.den : ℚ) * ((z 1).val j : ℚ) = r.num * ((z 0).val j : ℚ) by
      rw [ht, hrat]; ring)
  obtain ⟨q,hq⟩ : ∃ q, r.den = q+1 := Nat.exists_eq_succ_of_ne_zero r.den_ne_zero
  let A := ratDiagram q r.num (fun h ↦ hr (Rat.zero_of_num_zero h))
    (by rw [← hq]; exact r.isCoprime_num_den)
  obtain ⟨a,b,hab⟩ := r.isCoprime_num_den
  let x := fun j ↦ a * (z 1).val j + b * (z 0).val j
  have ex (i : Fin 2) (j : Fin n) : A.entry 0 i * x j = (z i).val j := by
    fin_cases i
    · change ((q+1 : ℕ) : ℤ) * (a * (z 1).val j + b * (z 0).val j) = (z 0).val j
      rw [← hq]
      linear_combination a * rr j + (z 0).val j * hab
    · change r.num * (a * (z 1).val j + b * (z 0).val j) = (z 1).val j
      linear_combination -b * rr j + (z 1).val j * hab
  have hx : x ≠ 0 := by
    intro h; apply (z 0).property; funext j; simpa [h] using (ex 0 j).symm
  exact ⟨⟨q,A,x,hx⟩, Subtype.ext (funext fun i ↦ Subtype.ext (funext (ex i)))⟩

theorem orderTwo_line_reindex (n : ℕ) (D : Set (SL n)) (F : (Fin 2 → E n) → ℝ≥0∞) :
    (∑' z : ↥((orderTwoIndependent n)ᶜ), orderTwoOrbit D F z.val) =
      ∑' q, ∑' A : Diagram 1 2 (q+1), ∑' z : NonzeroIntVector n,
        vectorOrbitalIntegral D (fun x ↦ F (orderTwoLine A x)) z := by
  let e := Equiv.ofBijective _ (And.intro (@linePair_injective n) linePair_surjective)
  rw [← e.tsum_eq (fun z ↦ orderTwoOrbit D F z.val)]
  refine (tsum_sigma (f := fun q t ↦ orderTwoOrbit D F (lineIntegerPair (n := n) ⟨q,t⟩))).trans ?_
  apply tsum_congr
  intro q
  refine (tsum_sigma (f := fun A z ↦ orderTwoOrbit D F (lineIntegerPair (n := n) ⟨q,A,z⟩))).trans ?_
  apply tsum_congr
  intro A
  apply tsum_congr
  intro z
  apply lintegral_congr
  intro g
  apply congrArg F
  funext j
  apply WithLp.ofLp_injective 2
  change g.val.mulVec (fun i ↦ ((A.entry 0 j * z.val i : ℤ) : ℝ)) =
    (A.entry 0 j : ℝ) • g.val.mulVec (fun i ↦ (z.val i : ℝ))
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  push_cast
  rfl

end SigabaNeo.Rogers
