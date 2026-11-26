import Definitions.Def_WE_XWE
import Mathlib.Algebra.Order.Chebyshev

open SigabaNeo AdvancedEncryption.WE.XWE

theorem ctLaw_congr (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool)
    (b c : ℕ → Bool) (h : ∀ i < W2.length, b i = c i) :
    ctLaw S W1 W2 post b = ctLaw S W1 W2 post c := by
  unfold ctLaw
  congr 1
  funext msk
  congr 1
  funext ks
  have hm : (W2.mapIdx fun i w => S.enc msk w (b i)) = W2.mapIdx fun i w => S.enc msk w (c i) := by
    apply List.ext_getElem (by simp)
    intro n h1 _
    simp only [List.getElem_mapIdx]
    rw [h n (by simpa using h1)]
  rw [hm]

theorem hybLaw_zero (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool) :
    hybLaw S W1 W2 post 0 = xweLaw S W1 W2 post false :=
  ctLaw_congr S W1 W2 post _ _ fun i _ => by simp

theorem hybLaw_length (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool) :
    hybLaw S W1 W2 post W2.length = xweLaw S W1 W2 post true :=
  ctLaw_congr S W1 W2 post _ _ fun i hi => by simp [hi]

/-- **Security of XWE from per-ciphertext hops.** If switching one ABE ciphertext (hop
`j → j + 1`) is a decision problem with `k` bits for every `j < |W2|`, then every machine
distinguishing the XWE encryptions of `false` and `true` has `2^k · gain ≤ |W2|² · cost`. -/
theorem solution (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool) (k : ℕ)
    (hop : ∀ j < W2.length,
      (Problem.decision (hybLaw S W1 W2 post j) (hybLaw S W1 W2 post (j + 1))).HardAt k)
    (A : Machine) :
    (2 : ℝ) ^ k *
        (Problem.decision (xweLaw S W1 W2 post false) (xweLaw S W1 W2 post true)).gain A ≤
      (W2.length : ℝ) ^ 2 * A.cost := by
  set D := hybLaw S W1 W2 post
  set T := W2.length
  rw [← hybLaw_zero, ← hybLaw_length]
  have hc : (Problem.decision (D 0) (D T)).gain A ≤
      T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A := by
    simp only [Problem.gain]
    have htel : A.acceptProb (D 0) - A.acceptProb (D T) =
        ∑ i ∈ Finset.range T, (A.acceptProb (D i) - A.acceptProb (D (i + 1))) := by
      rw [Finset.sum_range_sub' (fun i => A.acceptProb (D i))]
    rw [htel]
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range T)
      (f := fun i => A.acceptProb (D i) - A.acceptProb (D (i + 1)))
  have hsum : (2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A ≤
      T * A.cost := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range T, (2 : ℝ) ^ k * (Problem.decision (D i) (D (i + 1))).gain A
        ≤ ∑ _i ∈ Finset.range T, (A.cost : ℝ) :=
          Finset.sum_le_sum fun i hi => hop i (Finset.mem_range.mp hi) A
      _ = T * A.cost := by simp
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc (2 : ℝ) ^ k * (Problem.decision (D 0) (D T)).gain A
      ≤ (2 : ℝ) ^ k * (T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = T * ((2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) := by
        ring
    _ ≤ T * (T * A.cost) := mul_le_mul_of_nonneg_left hsum hT
    _ = (T : ℝ) ^ 2 * A.cost := by ring

