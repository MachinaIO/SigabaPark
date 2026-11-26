module

public import Definitions.Def_LatticeAttack_QAry_MainRowSpaces

set_option autoImplicit true

/-! # Marked partition arrays

A block carries a free point. Occurrences copy that point or reflect it through
the mark via x ↦ v-x. Labelled choices include a deterministic centre at any
slot. All results are finite and use no continuum or integration hypothesis.
-/

public section
namespace SigabaNeo.QAry

open Finset

/-- Rows in the order used for the marked moment (mark first). -/
def partitionRows {K : Type*} [Field K] {m k b : ℕ} (v : Fin m → K)
    (x : Fin b → Fin m → K) (parent : Fin k → Fin b) (reflect : Fin k → Bool) :
    Matrix (Fin (k+1)) (Fin m) K :=
  Fin.cons v fun i ↦ if reflect i then v - x (parent i) else x (parent i)

def freeRows {K : Type*} {m b : ℕ} (v : Fin m → K) (x : Fin b → Fin m → K) :
    Matrix (Fin (b+1)) (Fin m) K := Fin.cons v x

/-- Recovering each parent from one occurrence proves rank preservation even
when the chosen occurrence is reflected or the free points are dependent. -/
theorem partitionRows_rank {K : Type*} [Field K] {m k b : ℕ} (v : Fin m → K)
    (x : Fin b → Fin m → K) (parent : Fin k → Fin b) (hp : Function.Surjective parent)
    (reflect : Fin k → Bool) :
    (partitionRows v x parent reflect).rank = (freeRows v x).rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  apply congrArg (fun U : Submodule K (Fin m → K) ↦ Module.finrank K U)
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨j, rfl⟩
    have mem (i) := Submodule.subset_span (R := K)
      (Set.mem_range_self (f := (freeRows v x).row) i)
    refine Fin.cases (mem 0) (fun i ↦ ?_) j
    change (if reflect i then v - x (parent i) else x (parent i)) ∈ _
    split
    · exact Submodule.sub_mem _ (mem 0) (mem (parent i).succ)
    · exact mem (parent i).succ
  · rintro _ ⟨j, rfl⟩
    have mem (i) := Submodule.subset_span (R := K)
      (Set.mem_range_self (f := (partitionRows v x parent reflect).row) i)
    refine Fin.cases (mem 0) (fun a ↦ ?_) j
    obtain ⟨i, rfl⟩ := hp a
    have h := mem i.succ
    change (if reflect i then v - x (parent i) else x (parent i)) ∈ _ at h
    change x (parent i) ∈ Submodule.span K _
    split at h
    · simpa only [sub_sub_cancel] using Submodule.sub_mem _ (show v ∈ _ from mem 0) h
    · exact h

/-- None chooses a centre. An occurrence records its block representative and
orientation. Canonical partitions use the first label of each block. -/
abbrev LabelPattern (p : ℕ) := Fin p → Option (Fin p × Bool)

def pivotCount {p : ℕ} (a : LabelPattern p) : ℕ :=
  1 + (univ.filter fun i ↦ ∃ j, (a j).map Prod.fst = some i).card

noncomputable def pivotErrorBound (m k B : ℕ) (E scale : ℝ) : ℝ :=
  (∑ d ∈ range k, ((((2*B+1)^k)^d * ((2*B+1)^d)^m : ℕ) : ℝ) * E) / scale^(k*m)

open Classical in
/-- Total independence error with the original pivot weight for each pattern.
The workload and the signed centre factors may both be included in w. -/
theorem labelledPivotError {p m B : ℕ} (P : Finset (LabelPattern p))
    (S : (a : LabelPattern p) → Finset (Matrix (Fin m) (Fin (pivotCount a)) ℤ))
    (w : (a : LabelPattern p) → Matrix (Fin m) (Fin (pivotCount a)) ℤ → ℝ)
    (bound : ∀ a ∈ P, ∀ X ∈ S a, ∀ i j, |X i j| ≤ (B : ℤ))
    (E scale : ℝ) (hs : 0 ≤ scale) (hE : 0 ≤ E)
    (hw : ∀ a ∈ P, ∀ X ∈ S a, |w a X| ≤ E) :
    |(∑ a ∈ P, (∑ X ∈ S a, w a X) / scale^(pivotCount a*m)) -
      ∑ a ∈ P, (∑ X ∈ S a with (X.map (Int.castRingHom ℚ)).rank = pivotCount a,
        w a X) / scale^(pivotCount a*m)| ≤
      ∑ a ∈ P, pivotErrorBound m (pivotCount a) B E scale := by
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun a ha ↦
    freeingPivotError (S a) (bound a ha) (w a) E scale hs hE (hw a ha))

theorem labelPatternCount {p : ℕ} (P : Finset (LabelPattern p)) :
    P.card ≤ (2*p+1)^p := by
  simpa [LabelPattern, Nat.mul_comm] using P.card_le_univ

theorem pivotCount_le {p : ℕ} (a : LabelPattern p) : pivotCount a ≤ p+1 := by
  unfold pivotCount
  have h := (univ.filter fun i ↦ ∃ j, (a j).map Prod.fst = some i).card_le_univ
  simp only [Fintype.card_fin] at h
  omega

/-- A uniform total error, including all centre choices, orientations and partitions. -/
theorem sum_pivotErrorBound_le {p m B : ℕ} (P : Finset (LabelPattern p))
    (E scale : ℝ) (hs : 0 ≤ scale) (hE : 0 ≤ E) :
    (∑ a ∈ P, pivotErrorBound m (pivotCount a) B E scale) ≤
      ((2*p+1)^p : ℕ) * ∑ k ∈ range (p+2), pivotErrorBound m k B E scale := by
  have hn (k) : 0 ≤ pivotErrorBound m k B E scale := by
    unfold pivotErrorBound
    positivity
  calc
    _ ≤ ∑ _a ∈ P, ∑ k ∈ range (p+2), pivotErrorBound m k B E scale :=
      sum_le_sum fun a _ ↦ single_le_sum (fun i _ ↦ hn i)
        (mem_range.mpr (Nat.lt_succ_of_le (pivotCount_le a)))
    _ = (P.card : ℝ) * ∑ k ∈ range (p+2), pivotErrorBound m k B E scale := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast labelPatternCount P)
      (sum_nonneg fun i _ ↦ hn i)

/-- Free pivots range independently over the same discrete fibre. Summing one
factor per block gives the product of the discrete block masses. -/
theorem freeBlockMass {α : Type*} [Fintype α] {b : ℕ} (w : Fin b → α → ℝ) :
    (∑ x : Fin b → α, ∏ i, w i (x i)) = ∏ i, ∑ y, w i y := by
  exact (Fintype.prod_sum ..).symm

/-- Tuples in a fixed oriented pattern, with every reconstructed point in
the discrete fibre. -/
def patternTuple {m k b : ℕ} (v : Fin m → ℤ) (s : Finset (Fin m → ℤ))
    (parent : Fin k → Fin b) (reflect : Fin k → Bool)
    (closed : ∀ i, reflect i = true → ∀ y ∈ s, v - y ∈ s)
    (x : Fin b → s) (i : Fin k) : s :=
  if h : reflect i then ⟨v - (x (parent i)).val, closed i h _ (x _).property⟩
  else x (parent i)

theorem patternTuple_injective {m k b : ℕ} (v : Fin m → ℤ) (s : Finset (Fin m → ℤ))
    (parent : Fin k → Fin b) (hp : Function.Surjective parent) (reflect : Fin k → Bool)
    (closed : ∀ i, reflect i = true → ∀ y ∈ s, v - y ∈ s) :
    Function.Injective (patternTuple v s parent reflect closed) := by
  intro x y h
  funext a
  obtain ⟨i, rfl⟩ := hp a
  have he := congrArg Subtype.val (congrFun h i)
  cases hr : reflect i <;> simpa [patternTuple, hr] using he

open Classical in
/-- The modular rank weight in the marked raw sum, restricted to the image
of one oriented pattern, expressed exactly as a sum over its block pivots. -/
theorem partitionRawSum {q m k b : ℕ} [Fact q.Prime] (v : Fin m → ℤ)
    (s : Finset (Fin m → ℤ)) (parent : Fin k → Fin b) (hp : Function.Surjective parent)
    (reflect : Fin k → Bool) (closed : ∀ i, reflect i = true → ∀ y ∈ s, v-y ∈ s)
    (weight : ℕ → ℝ) :
    (∑ z ∈ univ.image (patternTuple v s parent reflect closed),
      weight (freeRows (fun j ↦ (v j : ZMod q)) (fun i j ↦ ((z i).val j : ZMod q))).rank) =
    ∑ x : Fin b → s,
      weight (freeRows (fun j ↦ (v j : ZMod q)) (fun i j ↦ ((x i).val j : ZMod q))).rank := by
  rw [sum_image (fun _ _ _ _ h ↦ patternTuple_injective v s parent hp reflect closed h)]
  apply sum_congr rfl
  intro x _
  let V := fun j ↦ (v j : ZMod q)
  let X := fun i j ↦ ((x i).val j : ZMod q)
  have he : freeRows V (fun i j ↦ ((patternTuple v s parent reflect closed x i).val j : ZMod q)) =
      partitionRows V X parent reflect := by
    ext i j
    refine Fin.cases rfl (fun l ↦ ?_) i
    cases hr : reflect l <;> simp [freeRows, partitionRows, patternTuple, hr, X, V]
  exact congrArg weight ((congrArg Matrix.rank he).trans (partitionRows_rank V X parent hp reflect))

/-- Exact singleton cancellation for discrete block weights, including the
orientation multiplicity in each block weight. -/
theorem centeredFreeBlockMass {p : ℕ} {α : Type*} [Fintype α]
    (P : Finset (Finset (Finset (Fin p)))) (w : Finset (Fin p) → α → ℝ) (M : ℝ) :
    (∑ blocks ∈ P, (∏ B ∈ blocks, ∑ x, w B x) *
      ∑ a ∈ (univ \ blocks.biUnion id).powerset,
        M ^ a.card * (-M) ^ ((univ \ blocks.biUnion id) \ a).card) =
    ∑ blocks ∈ P with univ ⊆ blocks.biUnion id, ∏ B ∈ blocks, ∑ x, w B x :=
  centeredPartitionSum P univ _ _ M

/-- After cancellation a partition of 2h labels has at most h blocks. -/
theorem survivingBlockCount {h : ℕ} (blocks : Finset (Finset (Fin (2*h))))
    (disj : (blocks : Set (Finset (Fin (2*h)))).PairwiseDisjoint id)
    (large : ∀ B ∈ blocks, 2 ≤ B.card) : blocks.card ≤ h := by
  have hc := (blocks.biUnion id).card_le_univ
  rw [card_biUnion disj, Fintype.card_fin] at hc
  have hl := sum_le_sum large
  simp only [sum_const, smul_eq_mul] at hl
  change ∑ B ∈ blocks, B.card ≤ 2*h at hc
  omega

/-- With box width at most scale*C, every deficient stratum saves at least
one spatial power of the scale. The row-space enumeration is paid only once. -/
theorem pivotErrorBound_le {m k B : ℕ} {E scale C : ℝ}
    (hs : 1 ≤ scale) (hC : 1 ≤ C) (hB : ((2*B+1 : ℕ) : ℝ) ≤ scale*C)
    (hE : 0 ≤ E) :
    pivotErrorBound m k B E scale ≤
      k * ((2*B+1 : ℕ) : ℝ)^(k*k) * C^(k*m) * E / scale^m := by
  let W : ℝ := (2*B+1 : ℕ)
  have hW : 1 ≤ W := by dsimp [W]; exact_mod_cast (by omega : 1 ≤ 2*B+1)
  have hs0 : 0 < scale := by linarith
  have hC0 : 0 ≤ C := by linarith
  have each (d : ℕ) (hd : d ∈ range k) :
      ((W^k)^d * (W^d)^m * E) * scale^m ≤
        W^(k*k) * C^(k*m) * E * scale^(k*m) := by
    have hd' := mem_range.mp hd
    have h₁ := pow_le_pow_right₀ hW (Nat.mul_le_mul_left k hd'.le)
    have h₂ := pow_le_pow_left₀ (le_trans zero_le_one hW) hB (d*m)
    have h₃ := pow_le_pow_right₀ hC (Nat.mul_le_mul_right m hd'.le)
    have h₄ := pow_le_pow_right₀ hs (Nat.mul_le_mul_right m hd')
    rw [Nat.succ_mul, pow_add] at h₄
    rw [mul_pow] at h₂
    rw [← pow_mul, ← pow_mul]
    calc
      _ ≤ (W^(k*k) * (scale^(d*m)*C^(d*m)) * E) * scale^m := by gcongr
      _ = W^(k*k) * C^(d*m) * E * (scale^(d*m)*scale^m) := by ring
      _ ≤ _ := by gcongr
  unfold pivotErrorBound
  apply (div_le_div_iff₀ (pow_pos hs0 _) (pow_pos hs0 _)).mpr
  push_cast
  rw [sum_mul]
  calc
    _ ≤ ∑ _d ∈ range k, W^(k*k)*C^(k*m)*E*scale^(k*m) := by
      apply sum_le_sum
      intro d hd
      simpa [W] using each d hd
    _ = _ := by simp [W]; ring

/-- Bound the surviving block products, including orientation choices, by a
single moment power. The finite family can be any collection of partitions. -/
theorem survivingPartitionMass_le {h : ℕ} (P : Finset (Finset (Finset (Fin (2*h)))))
    (w : Finset (Fin (2*h)) → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (disj : ∀ blocks ∈ P, (blocks : Set (Finset (Fin (2*h)))).PairwiseDisjoint id)
    (large : ∀ blocks ∈ P, ∀ B ∈ blocks, 2 ≤ B.card)
    (hw : ∀ blocks ∈ P, ∀ B ∈ blocks, |w B| ≤ 2^(B.card-1)*M) :
    |∑ blocks ∈ P with univ ⊆ blocks.biUnion id, ∏ B ∈ blocks, w B| ≤
      P.card * (2^(2*h) * M^h) := by
  classical
  let T := P.filter fun blocks ↦ univ ⊆ blocks.biUnion id
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _blocks ∈ T, (2^(2*h) * M^h) := by
      apply sum_le_sum
      intro blocks hb
      have hP := (mem_filter.mp hb).1
      have hcount := survivingBlockCount blocks (disj blocks hP) (large blocks hP)
      have hcard := (blocks.biUnion id).card_le_univ
      rw [card_biUnion (disj blocks hP), Fintype.card_fin] at hcard
      have hsum : (∑ B ∈ blocks, (B.card-1)) ≤ 2*h :=
        (sum_le_sum fun B _ ↦ Nat.sub_le B.card 1).trans hcard
      rw [abs_prod]
      calc
        _ ≤ ∏ B ∈ blocks, (2^(B.card-1)*M) :=
          prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (hw blocks hP)
        _ = (2:ℝ)^(∑ B ∈ blocks, (B.card-1)) * M^blocks.card := by
          rw [prod_mul_distrib, ← prod_pow_eq_pow_sum, prod_const]
        _ ≤ _ := mul_le_mul (pow_le_pow_right₀ (by norm_num) hsum)
          (pow_le_pow_right₀ hM hcount) (by positivity) (by positivity)
    _ = (T.card : ℝ) * _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le ..) (by positivity)

#print axioms survivingPartitionMass_le
#print axioms survivingBlockCount
#print axioms pivotErrorBound_le
#print axioms centeredFreeBlockMass
#print axioms partitionRawSum
#print axioms sum_pivotErrorBound_le
#print axioms freeBlockMass
#print axioms partitionRows_rank
#print axioms labelledPivotError
#print axioms labelPatternCount

end SigabaNeo.QAry
