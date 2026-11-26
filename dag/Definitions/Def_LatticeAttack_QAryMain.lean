module

public import Definitions.Def_LatticeAttack_QAry_RankDefect
public import Definitions.Def_LatticeAttack_QAry_MainCounting
public import Definitions.Def_LatticeAttack_QAry_MainRowSpaces
public import Definitions.Def_LatticeAttack_QAry_MainPatterns
public import Definitions.Def_LatticeAttack_Reduction_Sieve_Core

set_option autoImplicit true

/-! # Finite marked kernel moments

The exact expansion below assumes only primality of the modulus. The mark and every
occurrence are integer vectors, so a finite fibre can impose arbitrary shell or lens tests.
The centre may depend on the mark. The finite static bound assumes positive population,
degree and terminal references. Its centre errors must be at most V/200, α/4 and β/4
respectively. The rank-stratum identity has no geometric hypotheses. Estimating these
stratum sizes, controlling the rational diagram sum and deriving the T4b exponential
rate remain open here. No continuum estimates are assumed.
-/

public section
namespace SigabaNeo.QAry
open Finset
open scoped NNReal

variable {q n m : ℕ} [Fact q.Prime]
abbrev CheckMatrix (q n m : ℕ) := Fin n → Fin m → ZMod q
abbrev GridPoint (m : ℕ) := Fin m → ℤ

def inKernel (A : CheckMatrix q n m) (v : GridPoint m) : Prop :=
  ∀ i, (fun j ↦ (v j : ZMod q)) ⬝ᵥ A i = 0

noncomputable def fibreCount (A : CheckMatrix q n m) (s : Finset (GridPoint m)) : ℝ := by
  classical exact ∑ x ∈ s, if inKernel A x then 1 else 0

def markedRows {k : ℕ} (v : GridPoint m) (xs : Fin k → GridPoint m) :
    Matrix (Fin (k+1)) (Fin m) (ZMod q) :=
  Fin.cons (fun j ↦ (v j : ZMod q)) (fun i j ↦ (xs i j : ZMod q))

open Classical in
theorem markedRawSum (v : GridPoint m) (s : Finset (GridPoint m)) (k : ℕ) :
    (∑ A : CheckMatrix q n m, if inKernel A v then fibreCount A s ^ k else 0) =
    ∑ xs : Fin k → s, (q : ℝ) ^ ((m - (markedRows (q := q) v (fun i ↦ xs i)).rank) * n) := by
  classical
  have h (A : CheckMatrix q n m) :
      fibreCount A s = ∑ x : s, (if inKernel A x then (1 : ℝ) else 0) := by
    simp [fibreCount, ← Finset.sum_attach s]
  simp_rw [h, Fintype.sum_pow]
  calc
    _ = ∑ A : CheckMatrix q n m, ∑ xs : Fin k → s,
        if ∀ i, (markedRows v (fun j ↦ xs j)).mulVec (A i) = 0 then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro A _
      conv_lhs => rhs; rw [← Finset.sum_const_zero (s := (univ : Finset (Fin k → s))) (M := ℝ)]
      rw [← Finset.sum_ite_irrel]
      apply sum_congr rfl
      intro xs _
      have hh : (∀ i, (markedRows v (fun j ↦ xs j)).mulVec (A i) = 0) ↔
          inKernel A v ∧ ∀ j, inKernel A (xs j) := by
        simp only [funext_iff, Matrix.mulVec, Pi.zero_apply, Fin.forall_fin_succ,
          markedRows, Fin.cons_zero, Fin.cons_succ, forall_and, inKernel]
        exact and_congr_right fun _ ↦ forall_comm
      by_cases hv : inKernel A v <;> simp [hh, hv, Finset.prod_ite_zero]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro xs _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
      exact_mod_cast kernelCount n (markedRows (q := q) v (fun j ↦ xs j))

open Classical in
theorem markedCenteredSum (v : GridPoint m) (s : Finset (GridPoint m)) (c : ℝ) (p : ℕ) :
    (∑ A : CheckMatrix q n m, if inKernel A v then (fibreCount A s - c)^p else 0) =
    ∑ k ∈ range (p+1), ((∑ xs : Fin k → s,
      (q : ℝ) ^ ((m - (markedRows (q := q) v (fun i ↦ xs i)).rank) * n)) *
      (-c)^(p-k) * p.choose k) := by
  classical
  simp_rw [← markedRawSum (q := q) (n := n), sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  by_cases hv : inKernel A v <;> simp [hv, sub_eq_add_neg, add_pow]

/-- Exact unnormalized centred moment in modular-rank coordinates. -/
noncomputable def rankMoment (q n : ℕ) {m : ℕ} (v : GridPoint m)
    (s : Finset (GridPoint m)) (c : ℝ) (p : ℕ) [Fact q.Prime] : ℝ :=
  ∑ k ∈ range (p+1), (∑ xs : Fin k → s,
    (q : ℝ) ^ ((m - (markedRows (q := q) v (fun i ↦ xs i)).rank) * n)) *
    (-c)^(p-k) * p.choose k

open Classical in
/-- Simultaneous Markov bound over marks, bands and radii, allowing different thresholds
and orders at each index. The left side is uniform matrix probability. -/
theorem markedDeviationUnion {ι : Type*} (I : Finset ι) (mark : ι → GridPoint m)
    (s : ι → Finset (GridPoint m)) (c t : ι → ℝ) (h : ι → ℕ) (ht : ∀ j ∈ I, 0 < t j) :
    ((univ.filter (fun A : CheckMatrix q n m ↦ ∃ j ∈ I, inKernel A (mark j) ∧
      t j ≤ |fibreCount A (s j) - c j|)).card : ℝ) / q^(m*n) ≤
    (∑ j ∈ I, rankMoment q n (mark j) (s j) (c j) (2*h j) / t j^(2*h j)) / q^(m*n) := by
  classical
  apply div_le_div_of_nonneg_right _ (by positivity)
  let bad (A : CheckMatrix q n m) := ∃ j ∈ I, inKernel A (mark j) ∧
    t j ≤ |fibreCount A (s j) - c j|
  let cost (A : CheckMatrix q n m) (j : ι) : ℝ :=
    (if inKernel A (mark j) then (fibreCount A (s j) - c j)^(2*h j) else 0) /
      t j^(2*h j)
  have nn (A) (j) (hj : j ∈ I) : 0 ≤ cost A j := by
    dsimp [cost]
    have htj := ht j hj
    rw [pow_mul]
    split_ifs <;> positivity
  calc
    _ = ∑ A : CheckMatrix q n m, if bad A then (1:ℝ) else 0 := by
      rw [← sum_filter]; simp [bad]
    _ ≤ ∑ A : CheckMatrix q n m, ∑ j ∈ I, cost A j := by
      apply sum_le_sum
      intro A _
      split_ifs with hb
      · obtain ⟨j, hj, hk, hd⟩ := hb
        apply le_trans _ (single_le_sum (nn A) hj)
        dsimp [cost]
        rw [ite_eq_left hk, le_div_iff₀ (pow_pos (ht j hj) _), one_mul]
        simpa [pow_mul, sq_abs] using pow_le_pow_left₀ (ht j hj).le hd (2*h j)
      · exact sum_nonneg (nn A)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [cost, ← sum_div]
      exact congrArg (· / t j^(2*h j)) (markedCenteredSum (mark j) (s j) (c j) (2*h j))

open SigabaNeo.Lattices.Sieve

/-- Integer lifts with Euclidean length between two physical radii. Multiplying normalized
sieve radii by the mesh denominator gives these physical radii. -/
noncomputable def gridAnnulus (m : ℕ) (lo hi : ℝ) : Finset (GridPoint m) := by
  classical
  exact (Fintype.piFinset fun _ ↦ Icc (-⌈hi⌉) ⌈hi⌉).filter fun x ↦
    lo^2 ≤ ∑ i, (x i : ℝ)^2 ∧ (∑ i, (x i : ℝ)^2) ≤ hi^2

theorem mem_gridAnnulus {lo hi : ℝ} (hhi : 0 ≤ hi) (x : GridPoint m) :
    x ∈ gridAnnulus m lo hi ↔ lo^2 ≤ ∑ i, (x i : ℝ)^2 ∧ (∑ i, (x i : ℝ)^2) ≤ hi^2 := by
  classical
  refine ⟨fun hx ↦ (mem_filter.mp hx).2, fun hx ↦ mem_filter.mpr ⟨?_,hx⟩⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hh := (single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin m))) ↦ sq_nonneg (x j : ℝ))
    (mem_univ i)).trans hx.2
  have hc := Int.le_ceil hi
  have hl : -(⌈hi⌉ : ℝ) ≤ (x i : ℝ) := by nlinarith
  have hu : (x i : ℝ) ≤ (⌈hi⌉ : ℝ) := by nlinarith
  exact mem_Icc.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

open Classical in
noncomputable def kernelShell (A : CheckMatrix q n m) (S : Finset (GridPoint m)) :=
  S.filter (inKernel A)

private theorem fibreCount_card (A : CheckMatrix q n m) (S : Finset (GridPoint m)) :
    fibreCount A S = (kernelShell A S).card := by
  classical simp [fibreCount, kernelShell]

private theorem kernel_sub {A : CheckMatrix q n m} {u v : GridPoint m}
    (hu : inKernel A u) (hv : inKernel A v) : inKernel A (u-v) := by
  intro i
  simpa [Pi.sub_apply, Int.cast_sub, dotProduct, sub_mul, sum_sub_distrib] using
    sub_eq_zero.mpr ((hu i).trans (hv i).symm)

private theorem kernel_add {A : CheckMatrix q n m} {u v : GridPoint m}
    (hu : inKernel A u) (hv : inKernel A v) : inKernel A (u+v) := by
  intro i
  simpa [Pi.add_apply, Int.cast_add, dotProduct, add_mul, sum_add_distrib] using
    congrArg₂ (· + ·) (hu i) (hv i)

theorem population_of_deviation (A : CheckMatrix q n m) (S : Finset (GridPoint m))
    {V : ℝ} (hV : 0 < V) (h : |fibreCount A S - V| ≤ V/100) :
    ∃ θ, S1 (kernelShell A S) V θ := by
  rw [fibreCount_card] at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  refine ⟨((kernelShell A S).card - V) / V, ⟨?_, ?_, ?_⟩⟩
  · field_simp
    ring
  · apply (le_div_iff₀ hV).mpr
    linarith
  · apply (div_le_iff₀ hV).mpr
    linarith

theorem degrees_of_deviation (A : CheckMatrix q n m) (S T : Finset (GridPoint m))
    {α β : ℝ}
    (ha : ∀ u ∈ kernelShell A S, |fibreCount A (S.filter (fun c ↦ u-c ∈ T)) - α| ≤ α/2)
    (hb : ∀ d ∈ kernelShell A T, |fibreCount A (S.filter (fun c ↦ d+c ∈ S)) - β| ≤ β/2) :
    S2 (kernelShell A S) (kernelShell A T) α β := by
  classical
  constructor
  · intro u hu
    obtain ⟨lo, hi⟩ := abs_le.mp (ha u hu)
    have he : (kernelShell A S).filter (fun c ↦ u-c ∈ kernelShell A T) =
        kernelShell A (S.filter (fun c ↦ u-c ∈ T)) := by
      ext c
      simp only [kernelShell, mem_filter] at *
      exact ⟨fun h ↦ ⟨⟨h.1.1,h.2.1⟩,h.1.2⟩,
        fun h ↦ ⟨⟨h.1.1,h.2⟩,h.1.2,kernel_sub hu.2 h.2⟩⟩
    dsimp only
    rw [he, ← fibreCount_card]
    constructor <;> linarith
  · intro d hd
    obtain ⟨lo, hi⟩ := abs_le.mp (hb d hd)
    have he : (kernelShell A S).filter (fun c ↦ d+c ∈ kernelShell A S) =
        kernelShell A (S.filter (fun c ↦ d+c ∈ S)) := by
      ext c
      simp only [kernelShell, mem_filter] at *
      exact ⟨fun h ↦ ⟨⟨h.1.1,h.2.1⟩,h.1.2⟩,
        fun h ↦ ⟨⟨h.1.1,h.2⟩,h.1.2,kernel_add hd.2 h.2⟩⟩
    dsimp only
    rw [he, ← fibreCount_card]
    constructor <;> linarith

theorem coverage_of_deviation (A : CheckMatrix q n m) (S B : Finset (GridPoint m))
    (M : GridPoint m → ℝ)
    (h : ∀ d ∈ kernelShell A B, |fibreCount A (S.filter (fun c ↦ d+c ∈ S)) - M d| < M d) :
    S3prime (kernelShell A S) (kernelShell A B : Set (GridPoint m)) := by
  classical
  intro d hd
  obtain ⟨hl, _⟩ := abs_lt.mp (h d hd)
  have hp : 0 < fibreCount A (S.filter (fun c ↦ d+c ∈ S)) := by linarith
  rw [fibreCount_card, Nat.cast_pos, Finset.card_pos] at hp
  obtain ⟨c, hc⟩ := hp
  change d ∈ kernelShell A B at hd
  simp only [kernelShell, mem_filter] at hc hd
  exact ⟨d+c, mem_filter.mpr ⟨hc.1.2, kernel_add hd.2 hc.2⟩,
    c, mem_filter.mpr ⟨hc.1.1,hc.2⟩, add_sub_cancel_right _ _⟩

structure FibreTest (m : ℕ) where
  v : GridPoint m
  s : Finset (GridPoint m)
  c : ℝ
  t : ℝ
  h : ℕ

open Classical in
noncomputable def staticTests {m : ℕ} (depth h : ℕ) (S : ℕ → Finset (GridPoint m))
    (V α β μ : ℕ → ℝ) (a b : ℕ → GridPoint m → ℝ) (B : Finset (GridPoint m)) (M : GridPoint m → ℝ) :
    Finset (FibreTest m) :=
  ((range (depth+1)).image fun i ↦ ⟨0, S i, μ i, V i/200, 1⟩) ∪
  ((range depth).biUnion fun i ↦ (S i).image fun u ↦
    ⟨u, (S i).filter (fun c ↦ u-c ∈ S (i+1)), a i u, α i/4, h⟩) ∪
  ((range depth).biUnion fun i ↦ (S (i+1)).image fun d ↦
    ⟨d, (S i).filter (fun c ↦ d+c ∈ S i), b i d, β i/4, h⟩) ∪
  (B.image fun d ↦ ⟨d, (S depth).filter (fun c ↦ d+c ∈ S depth), M d, M d, 1⟩)

open Classical in
/-- Uniform probability of failure of the three static sieve conditions, bounded by a
finite sum of modular ranks for the specified grid shells and terminal marks. -/
theorem staticFailure_le_rankSum (depth h : ℕ) (S : ℕ → Finset (GridPoint m))
    (V α β μ : ℕ → ℝ) (a b : ℕ → GridPoint m → ℝ) (B : Finset (GridPoint m)) (M : GridPoint m → ℝ)
    (hV : ∀ i ≤ depth, 0 < V i) (ha : ∀ i < depth, 0 < α i)
    (hb : ∀ i < depth, 0 < β i)
    (hμ : ∀ i ≤ depth, |μ i - V i| ≤ V i/200)
    (hac : ∀ i < depth, ∀ u ∈ S i, |a i u - α i| ≤ α i/4)
    (hbc : ∀ i < depth, ∀ d ∈ S (i+1), |b i d - β i| ≤ β i/4)
    (hM : ∀ d ∈ B, 0 < M d) :
    ((univ.filter (fun A : CheckMatrix q n m ↦ ¬
      ((∀ i ≤ depth, ∃ θ, S1 (kernelShell A (S i)) (V i) θ) ∧
       (∀ i < depth, S2 (kernelShell A (S i)) (kernelShell A (S (i+1))) (α i) (β i)) ∧
       S3prime (kernelShell A (S depth)) (kernelShell A B : Set (GridPoint m))))).card : ℝ) /
        q^(m*n) ≤
    (∑ j ∈ staticTests depth h S V α β μ a b B M,
      rankMoment q n j.v j.s j.c (2*j.h) / j.t^(2*j.h)) / q^(m*n) := by
  classical
  let I := staticTests depth h S V α β μ a b B M
  have ht : ∀ j ∈ I, 0 < j.t := by
    intro j hj
    simp only [I, staticTests, mem_union, mem_image, mem_biUnion, mem_range] at hj
    rcases hj with (((⟨i, hi, rfl⟩ | ⟨i, hi, u, _, rfl⟩) | ⟨i, hi, d, _, rfl⟩) | ⟨d, hd, rfl⟩)
    · exact div_pos (hV i (by omega)) (by norm_num)
    · exact div_pos (ha i hi) (by norm_num)
    · exact div_pos (hb i hi) (by norm_num)
    · exact hM d hd
  apply le_trans _ (markedDeviationUnion (q := q) (n := n) I
    FibreTest.v FibreTest.s FibreTest.c FibreTest.t FibreTest.h ht)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro A hA
  simp only [mem_filter, mem_univ, true_and] at hA ⊢
  by_contra hf
  push Not at hf
  apply hA
  simp only [I, staticTests, mem_union, mem_biUnion, mem_image, mem_range] at hf
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply population_of_deviation _ _ (hV i hi)
    have hh := hf ⟨0,S i,μ i,V i/200,1⟩
      (Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))) (by simp [inKernel, dotProduct])
    dsimp only at hh
    linarith [abs_sub_le (fibreCount A (S i)) (μ i) (V i), hμ i hi]
  · intro i hi
    apply degrees_of_deviation
    · intro u hu
      obtain ⟨hus, huk⟩ := mem_filter.mp hu
      have hh := hf ⟨_,_,_,_,h⟩ (Or.inl (Or.inl (Or.inr ⟨i,hi,u,hus,rfl⟩))) huk
      dsimp only at hh
      linarith [abs_sub_le (fibreCount A ((S i).filter (fun c ↦ u-c ∈ S (i+1)))) (a i u) (α i), hac i hi u hus]
    · intro d hd
      obtain ⟨hds, hdk⟩ := mem_filter.mp hd
      have hh := hf ⟨_,_,_,_,h⟩ (Or.inl (Or.inr ⟨i,hi,d,hds,rfl⟩)) hdk
      dsimp only at hh
      linarith [abs_sub_le (fibreCount A ((S i).filter (fun c ↦ d+c ∈ S i))) (b i d) (β i), hbc i hi d hds]
  · apply coverage_of_deviation _ _ _ M
    intro d hd
    obtain ⟨hds,hdk⟩ := mem_filter.mp hd
    exact hf ⟨_,_,_,_,1⟩ (Or.inr ⟨d,hds,rfl⟩) hdk

/-- Exact cost of replacing modular by rational ranks on an unweighted raw workload.
Only discrepant rank pairs enter. Each multiplicity is an integer point count. -/
theorem rankReplacement {k : ℕ} {ι : Type*} (S : Finset ι) (X : ι → Matrix (Fin k) (Fin m) ℤ)
    (q n : ℕ) [Fact q.Prime] :
    let u := fun x ↦ ((X x).map (Int.castRingHom (ZMod q))).rank
    let t := fun x ↦ ((X x).map (Int.castRingHom ℚ)).rank
    let ranks := fun x ↦ (t x, u x)
    (∑ x ∈ S, 1 / (q : ℝ)^(u x*n)) - (∑ x ∈ S, 1 / (q : ℝ)^(t x*n)) =
      ∑ p ∈ (S.image ranks).filter (fun p ↦ p.1 ≠ p.2),
        ((S.filter (fun x ↦ ranks x = p)).card : ℝ) *
          (1/(q : ℝ)^(p.2*n) - 1/(q : ℝ)^(p.1*n)) := by
  classical
  intro u t ranks
  let w (p : ℕ × ℕ) := 1/(q : ℝ)^(p.2*n) - 1/(q : ℝ)^(p.1*n)
  rw [← sum_sub_distrib]
  change (∑ x ∈ S, w (ranks x)) = _
  have hm : (S : Set ι).MapsTo ranks (S.image ranks) := fun x hx ↦ mem_image_of_mem _ hx
  rw [← sum_fiberwise_of_maps_to hm]
  rw [sum_filter]
  apply sum_congr rfl
  intro p _
  calc
    _ = ∑ _x ∈ S.filter (fun x ↦ ranks x = p), w p := by
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp hx).2]
    _ = _ := by
      by_cases he : p.1 = p.2 <;> simp [he, w, mul_sub]

open Classical in
/-- Probability that the kernel contains a grid mark in an exceptional inner ball.
The estimate applies to any finite short nonzero support, before testing terminal lenses. -/
theorem exceptionalMarkProbability (B : Finset (GridPoint m)) (R : ℝ)
    (hR : 1 ≤ R) (hq : R < q) (hs : ∀ x ∈ B, x ≠ 0 ∧ ∑ j, (x j : ℝ)^2 ≤ R^2) :
    ((univ.filter (fun A : CheckMatrix q n m ↦ (kernelShell A B).Nonempty)).card : ℝ≥0) /
      q^(m*n) ≤ B.card / (q : ℝ≥0)^n := by
  classical
  let X (x : GridPoint m) : Matrix (Fin 1) (Fin m) ℤ := fun _ ↦ x
  have hm := shortMeanValue (q := q) n B X (fun _ ↦ 1) R hR
    (fun x hx _ ↦ (hs x hx).2) (by simpa using hq)
  have hr (x) (hx : x ∈ B) : ((X x).map (Int.castRingHom ℚ)).rank = 1 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℚ (Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦
      (fun j ↦ (x j : ℚ))))) = 1
    rw [Set.range_const]
    apply finrank_span_singleton
    intro he
    apply (hs x hx).1
    ext j
    have hj : (x j : ℚ) = 0 := congrFun he j
    change x j = 0
    exact_mod_cast hj
  apply le_trans _ (le_of_eq (hm.trans ?_))
  · apply div_le_div_of_nonneg_right _ (by positivity)
    rw [show ((univ.filter (fun A : CheckMatrix q n m ↦ (kernelShell A B).Nonempty)).card :
      ℝ≥0) = ∑ A : CheckMatrix q n m,
        (if (kernelShell A B).Nonempty then (1 : ℝ≥0) else 0) by rw [← sum_filter]; simp]
    apply sum_le_sum
    intro A _
    split_ifs with ha
    · obtain ⟨x,hx⟩ := ha
      obtain ⟨hxB,hk⟩ := mem_filter.mp hx
      apply le_trans _ (single_le_sum (fun _ _ ↦ zero_le) hxB)
      have he : ∀ i, ((X x).map (Int.castRingHom (ZMod q))).mulVec (A i) = 0 :=
        fun i ↦ funext fun _ ↦ hk i
      rw [ite_eq_left he]
    · exact zero_le
  · calc
      _ = ∑ _x ∈ B, 1 / (q : ℝ≥0)^n := sum_congr rfl fun x hx ↦ by rw [hr x hx, one_mul]
      _ = _ := by simp [div_eq_mul_inv]

/-- Inner-ball term for a physical radius R strictly smaller than the modulus. -/
theorem innerBallProbability (R : ℝ) (hR : 1 ≤ R) (hq : R < q) :
    let B := (gridAnnulus m 0 R).erase 0
    ((univ.filter (fun A : CheckMatrix q n m ↦ (kernelShell A B).Nonempty)).card : ℝ≥0) /
      q^(m*n) ≤ B.card / (q : ℝ≥0)^n := by
  intro B
  apply exceptionalMarkProbability B R hR hq
  intro x hx
  obtain ⟨hn, hm⟩ := mem_erase.mp hx
  exact ⟨hn, ((mem_gridAnnulus (by linarith : 0 ≤ R) x).mp hm).2⟩

#print axioms innerBallProbability
#print axioms mem_gridAnnulus
#print axioms exceptionalMarkProbability
#print axioms rankReplacement
#print axioms staticFailure_le_rankSum
#print axioms population_of_deviation
#print axioms degrees_of_deviation
#print axioms coverage_of_deviation
#print axioms markedDeviationUnion
#print axioms markedRawSum
#print axioms markedCenteredSum
end SigabaNeo.QAry
