import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKLines

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers
namespace LineParam

abbrev Index (n k : ℕ) := Σ q : ℕ, Σ _ : Diagram 1 (k+1) (q+1), NonzeroIntVector n

private theorem entry_ne {k q} (A : Diagram 1 (k+1) (q+1)) (j) : A.entry 0 j ≠ 0 := by
  obtain ⟨i,h⟩ := A.nonzeroColumn j
  simpa only [Subsingleton.elim i 0] using h

private theorem first_entry {k q} (A : Diagram 1 (k+1) (q+1)) :
    A.entry 0 0 = (q+1 : ℕ) := by
  simpa [show A.pivot 0 = 0 from Fin.ext (A.first 0 rfl)] using A.pivotColumn 0 0

def tuple {n k} (t : Index n k) : IntegerTuple n (k+1) :=
  fun j ↦ ⟨t.2.1.entry 0 j • t.2.2.val, fun h ↦
    (smul_eq_zero.mp h).elim (entry_ne _ _) t.2.2.property⟩

abbrev Fiber (n k : ℕ) := (tupleRankIndex (n := n) (Nat.succ_pos k)) ⁻¹' {0}

def toFiber {n k} (t : Index n k) : Fiber n k := by
  refine ⟨tuple t, ?_⟩
  change tupleRankIndex _ _ = 0
  apply Fin.ext
  have hs : Submodule.span ℤ (Set.range fun i ↦ ((tuple t) i).val) ≤
      Submodule.span ℤ {t.2.2.val} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hr := Submodule.finrank_mono hs
  have ht := finrank_span_le_card (R := ℤ) ({t.2.2.val} : Set (Fin n → ℤ))
  classical
  have : tupleRank (tuple t) ≤ 1 := hr.trans (by simpa using ht)
  change tupleRank (tuple t) - 1 = 0
  omega

private theorem content_mul {k q} (A : Diagram 1 (k+1) (q+1)) (a : ℤ) :
    (Finset.univ.gcd fun j ↦ (A.entry 0 j * a).natAbs) = a.natAbs := by
  have hc : (Finset.univ.gcd fun j ↦ (A.entry 0 j).natAbs) = 1 := by
    apply A.primitive
    intro i j
    obtain rfl := Subsingleton.elim i 0
    exact Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ j))
  simp [Int.natAbs_mul, Finset.gcd_mul_right, normalize_eq, hc]

theorem injective {n k} : Function.Injective (@toFiber n k) := by
  rintro ⟨q,A,x⟩ ⟨s,B,y⟩ h
  have he (j : Fin (k+1)) (l : Fin n) : A.entry 0 j * x.val l = B.entry 0 j * y.val l :=
    congrArg (fun z : Fiber n k ↦ (z.val j).val l) h
  have same (l : Fin n) : x.val l = y.val l := by
    have ha := content_mul A (x.val l)
    simp_rw [he] at ha
    rw [content_mul] at ha
    have hp := he 0 l
    rw [first_entry, first_entry] at hp
    push_cast at hp
    rcases Int.natAbs_eq_natAbs_iff.mp ha with h | h
    · omega
    · by_cases hx : 0 ≤ x.val l
      · nlinarith [mul_nonneg (Int.natCast_nonneg q) hx, mul_nonneg (Int.natCast_nonneg s) hx]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg q) (le_of_not_ge hx),
          mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg s) (le_of_not_ge hx)]
  obtain rfl : x = y := Subtype.ext (funext same)
  obtain ⟨l,hl⟩ : ∃ l, x.val l ≠ 0 := by by_contra! H; exact x.property (funext H)
  have heq (j) := mul_right_cancel₀ hl (he j l)
  have hp := heq 0
  rw [first_entry, first_entry] at hp
  obtain rfl : q = s := by omega
  have hentry : A.entry = B.entry := funext fun i ↦ by
    obtain rfl := Subsingleton.elim i 0
    exact funext heq
  have hpiv : A.pivot = B.pivot := funext fun i ↦ by
    obtain rfl := Subsingleton.elim i 0
    exact Fin.ext ((A.first 0 rfl).trans (B.first 0 rfl).symm)
  obtain rfl : A = B := by cases A; cases B; congr
  rfl

private theorem positive_param {n k} (z : Fiber n k) (c : Fin (k+1) → ℤ)
    (x : Fin n → ℤ) (hc : 0 < c 0) (he : ∀ j, c j • x = (z.val j).val)
    (prim : ∀ d : ℕ, (∀ j, (d : ℤ) ∣ c j) → d = 1) :
    ∃ t, toFiber t = z := by
  have hc' (j) : c j ≠ 0 := fun h ↦ (z.val j).property (by rw [← he, h, zero_smul])
  have hx : x ≠ 0 := fun h ↦ (z.val 0).property (by rw [← he, h, smul_zero])
  let q := (c 0).toNat - 1
  have hq : ((q+1 : ℕ) : ℤ) = c 0 := by dsimp [q]; omega
  let A : Diagram 1 (k+1) (q+1) :=
    { entry := fun _ j ↦ c j
      pivot := fun _ ↦ 0
      increasing := Subsingleton.strictMono _
      first := by simp
      nonzeroColumn := fun j ↦ ⟨0, hc' j⟩
      pivotColumn := by intro i a; simp [Subsingleton.elim i a, hq]
      echelon := by simp
      primitive := fun d hd ↦ prim d (hd 0) }
  exact ⟨⟨q,A,x,hx⟩, Subtype.ext (funext fun j ↦ Subtype.ext (he j))⟩

theorem surjective {n k} : Function.Surjective (@toFiber n k) := by
  classical
  intro z
  let S := Submodule.span ℤ (Set.range fun i ↦ (z.val i).val)
  have hr : Module.finrank ℤ S = 1 := by
    have h := tupleRankIndex_succ (Nat.succ_pos k) z.val
    rw [show tupleRankIndex _ z.val = 0 from z.property] at h
    exact h.symm
  let b := Module.finBasisOfFinrankEq ℤ S hr
  let v (j) : S := ⟨(z.val j).val, Submodule.subset_span (Set.mem_range_self j)⟩
  let c (j) := b.repr (v j) 0
  have he (j) : c j • (b 0).val = (z.val j).val := by
    exact congrArg Subtype.val (show c j • b 0 = v j by
      simpa only [Fin.sum_univ_one] using b.sum_repr (v j))
  have prim (d : ℕ) (hd : ∀ j, (d : ℤ) ∣ c j) : d = 1 := by
    have all (x : S) : (d : ℤ) ∣ b.repr x 0 := by
      obtain ⟨x,hx⟩ := x
      induction hx using Submodule.span_induction with
      | mem x h => obtain ⟨j,rfl⟩ := h; exact hd j
      | zero => change _ ∣ b.repr (0 : S) 0; simp
      | add x y hx hy h₁ h₂ =>
        exact (show (d : ℤ) ∣ b.repr (⟨x,hx⟩ + ⟨y,hy⟩ : S) 0 by rw [map_add, Finsupp.add_apply]; exact dvd_add h₁ h₂)
      | smul a x hx h =>
        exact (show (d : ℤ) ∣ b.repr (a • (⟨x,hx⟩ : S)) 0 by
          rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact dvd_mul_of_dvd_right h a)
    exact Nat.dvd_one.mp (by exact_mod_cast (show (d : ℤ) ∣ 1 by simpa using all (b 0)))
  by_cases h : 0 < c 0
  · exact positive_param z c _ h he prim
  · have hn : c 0 ≠ 0 := fun hh ↦ (z.val 0).property (by rw [← he,hh,zero_smul])
    exact positive_param z (fun j ↦ -c j) (-(b 0).val) (by change 0 < -c 0; omega)
      (fun j ↦ by simpa using he j) (fun d hd ↦ prim d (fun j ↦ by simpa using hd j))

end LineParam

theorem rankOne_reindex (n k : ℕ) (D : Set (SL n)) (F : (Fin (k+1) → E n) → ℝ≥0∞) :
    rankOrbitSum (Nat.succ_pos k) D F 0 =
      ∑' q, ∑' A : Diagram 1 (k+1) (q+1), ∑' z : NonzeroIntVector n,
        vectorOrbitalIntegral D (fun x ↦ F (integerLineTuple A x)) z := by
  let e := Equiv.ofBijective _ (And.intro (@LineParam.injective n k) LineParam.surjective)
  let T (z : IntegerTuple n (k+1)) := ∫⁻ g in D,
    F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ))) ∂groupHaar n
  change (∑' z : LineParam.Fiber n k, T z.val) = _
  rw [← e.tsum_eq (fun z ↦ T z.val)]
  refine (tsum_sigma (f := fun q t ↦ T (LineParam.tuple ⟨q,t⟩))).trans ?_
  apply tsum_congr
  intro q
  refine (tsum_sigma (f := fun A z ↦ T (LineParam.tuple ⟨q,A,z⟩))).trans ?_
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

theorem rankOne_evaluation (n k : ℕ) (hn : 1 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin (k+1) → E n) → ℝ≥0∞) (hf : Measurable F) :
    rankOrbitSum (Nat.succ_pos k) D F 0 = groupHaar n D * rankDiagramTerm F 0 :=
  (rankOne_reindex n k D F).trans (rankOne_siegel_lines n k hn D hd hfin F hf)

end SigabaNeo.Rogers
