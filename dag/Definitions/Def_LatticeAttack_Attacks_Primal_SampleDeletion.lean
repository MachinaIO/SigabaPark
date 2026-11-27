module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionBall
public import Definitions.Def_LatticeAttack_Attacks_Primal_Planted
import all Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

public section
namespace SigabaNeo.SampleDeletion
open SigabaNeo.Planted

variable {m n q : ℕ} [Fact q.Prime]

/-- Dropping the last k sample coordinates keeps every secret coordinate and the height. -/
def prefixPoint {r k n : ℕ} (w : Coord (r+k) n → ℤ) : Coord r n → ℤ
  | .inl i => w (.inl (Fin.castAdd k i))
  | .inr j => w (.inr j)

/-- A solution of the punctured congruences always lifts, with no bound on the lift norm. -/
theorem prefix_member_iff {r k : ℕ} (A : Matrix (Fin (r+k)) (Fin n) (ZMod q))
    (e : Fin (r+k) → ℤ) (s : Fin n → ℤ) (z : Coord r n → ℤ) :
    member (fun i ↦ A (Fin.castAdd k i)) (fun i ↦ e (Fin.castAdd k i)) s z ↔
      ∃ w, member A e s w ∧ prefixPoint w = z := by
  constructor
  · intro h
    let residue (i : Fin (r+k)) : ZMod q :=
      (z last : ZMod q) * (A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i) -
        A i ⬝ᵥ (fun j ↦ (z (col j) : ZMod q))
    let w : Coord (r+k) n → ℤ := Sum.elim
      (Fin.addCases (fun i ↦ z (.inl i)) (fun j ↦ ((residue (Fin.natAdd r j)).val : ℤ)))
      (fun j ↦ z (.inr j))
    refine ⟨w, ?_, ?_⟩
    · intro i
      induction i using Fin.addCases with
      | left i => simpa [w, col, last] using h i
      | right j => simp [w, col, last, residue]
    · funext i
      cases i <;> simp [prefixPoint, w]
  · rintro ⟨w, hw, rfl⟩
    exact fun i ↦ hw (Fin.castAdd k i)

/-- Every retained design has the same number of completions in the uniform full matrix. -/
theorem prefix_design_card {r k : ℕ} (B : Matrix (Fin r) (Fin n) (ZMod q)) :
    Nat.card {A : Matrix (Fin (r+k)) (Fin n) (ZMod q) // (fun i ↦ A (Fin.castAdd k i)) = B} =
      q^(n*k) := by
  let equiv : {A : Matrix (Fin (r+k)) (Fin n) (ZMod q) // (fun i ↦ A (Fin.castAdd k i)) = B} ≃
      (Fin k → Fin n → ZMod q) :=
    { toFun := fun A i ↦ A.val (Fin.natAdd r i)
      invFun := fun C ↦ ⟨Fin.addCases B C, by
        funext i
        exact @Fin.addCases_left r k (fun _ ↦ Fin n → ZMod q) B C i⟩
      left_inv := fun A ↦ by
        apply Subtype.ext
        funext i
        induction i using Fin.addCases with
        | left i =>
          exact (@Fin.addCases_left r k (fun _ ↦ Fin n → ZMod q) B (fun j ↦ A.val (Fin.natAdd r j)) i).trans
            (congrFun A.property i).symm
        | right i => exact @Fin.addCases_right r k (fun _ ↦ Fin n → ZMod q) B (fun j ↦ A.val (Fin.natAdd r j)) i
      right_inv := fun C ↦ by
        funext i
        exact @Fin.addCases_right r k (fun _ ↦ Fin n → ZMod q) B C i }
  rw [Nat.card_congr equiv]
  simp [← pow_mul]

private noncomputable def fibre (q : ℕ) [Fact q.Prime] (e : Fin m → ℤ) (s : Fin n → ℤ)
    (z : Coord m n → ℤ) : Finset (Matrix (Fin m) (Fin n) (ZMod q)) := by
  classical
  exact Finset.univ.filter fun A ↦ member A e s z ∧ ¬ ∃ k : ℤ, z = k • plantedPoint e s

private theorem fibre_bound (e : Fin m → ℤ) (s : Fin n → ℤ) (R B : ℝ) (hR : 0 ≤ R)
    (he : ∀ i, |(e i : ℝ)| ≤ B) (hs : ∀ j, |(s j : ℝ)| ≤ B)
    (hq : R * Real.sqrt (1+B^2) < q) (z : Coord m n → ℤ) (hz : z ∈ integerBall R) :
    (fibre q e s z).card * q^m ≤ q^(n*m) := by
  classical
  let C := fibre q e s
  change (C z).card * _ ≤ _
  let t := z last
  let u : Fin n → ZMod q := (fun j ↦ (z (col j) : ZMod q)) - (t : ZMod q) • (fun j ↦ (s j : ZMod q))
  let v : Fin m → ZMod q := fun i ↦ (t : ZMod q) * e i - z (.inl i)
  have aff A (ha : A ∈ C z) : A.mulVec u = v := by
    ext i
    have hi := (Finset.mem_filter.mp ha).2.1 i
    change _ ⬝ᵥ (_ - _ • _) = _
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    dsimp [v,t]
    linear_combination hi
  by_cases hu : u = 0
  · suffices C z = ∅ by simp [this]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A ha
    have hv := aff A ha
    rw [hu, Matrix.mulVec_zero] at hv
    apply (Finset.mem_filter.mp ha).2.2
    refine ⟨t, funext fun i ↦ ?_⟩
    change z i = t * plantedPoint e s i
    by_cases hi : i = last
    · subst i; simp [t,last,plantedPoint]
    have hmod : (z i : ZMod q) = (t : ZMod q) * plantedPoint e s i := by
      cases i with
      | inl a => exact (sub_eq_zero.mp (congrFun hv.symm a)).symm
      | inr a =>
        cases a with
        | inl j => exact sub_eq_zero.mp (congrFun hu j)
        | inr l => exact (hi (by cases l; rfl)).elim
    have hb : |(plantedPoint e s i : ℝ)| ≤ B := by
      cases i with
      | inl a => exact he a
      | inr a =>
        cases a with
        | inl j => exact hs j
        | inr l => exact (hi (by cases l; rfl)).elim
    have hz' := ((mem_integerBall hR z).mp hz).2
    have hsum := Finset.sum_le_univ_sum_of_nonneg (s := {i,last}) (fun j ↦ sq_nonneg (z j : ℝ))
    simp only [Finset.sum_insert (by simpa using hi : i ∉ ({last} : Finset (Coord m n))), Finset.sum_singleton] at hsum
    have hd := discrepancy hR (hsum.trans hz') hb hq
    have hzmod : ((z i - t * plantedPoint e s i : ℤ) : ZMod q) = 0 := by simp [hmod]
    by_contra hn
    exact hd.not_ge (Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hn))
      ((dvd_abs _ _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzmod)))
  · exact le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card
      (fun A ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, aff A ha⟩))) (fibre_le u v hu)

private theorem real_sq {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    (normSq z : ℝ) = ∑ i, (z i : ℝ)^2 := by
  rw [normSq, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]

private theorem neg_mem (A : Matrix (Fin m) (Fin n) (ZMod q)) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (z : Coord m n → ℤ) (h : member A e s z) : member A e s (-z) := by
  intro i
  simpa only [Pi.neg_apply, Int.cast_neg, dotProduct, mul_neg, ← Finset.sum_neg_distrib, neg_mul, neg_add_rev, add_comm] using
    congrArg Neg.neg (h i)

private theorem pair_count (e : Fin m → ℤ) (s : Fin n → ℤ) (R B : ℝ) (hR : 0 ≤ R)
    (he : ∀ i, |(e i : ℝ)| ≤ B) (hs : ∀ j, |(s j : ℝ)| ≤ B)
    (hq : R * Real.sqrt (1+B^2) < q) :
    2 * (badMatrices q e s R).card * q^m ≤
      (integerBall (ι := Coord m n) R).card * q^(n*m) := by
  classical
  let T := integerBall (ι := Coord m n) R
  let C := fibre q e s
  let U := badMatrices q e s R
  have twice : 2 * U.card ≤ ∑ z ∈ T, (C z).card := by
    calc
      _ = ∑ _ ∈ U, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ A ∈ U, ∑ z ∈ T, (if A ∈ C z then 1 else 0) := by
        apply Finset.sum_le_sum
        intro A hA
        obtain ⟨z,hz,ha⟩ := Finset.mem_biUnion.mp (show A ∈ T.biUnion C from hA)
        have h := (Finset.mem_filter.mp ha).2
        have hne := ((mem_integerBall hR z).mp hz).1
        have hd : z ≠ -z := by
          intro hh
          apply hne
          ext i
          have := congrFun hh i
          simp only [Pi.neg_apply] at this
          change z i = 0
          omega
        have hnz : -z ∈ T := (mem_integerBall hR _).mpr ⟨neg_ne_zero.mpr hne, by
          simpa using ((mem_integerBall hR z).mp hz).2⟩
        have hna : A ∈ C (-z) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          neg_mem _ _ _ _ h.1, by
            rintro ⟨k,hk⟩
            exact h.2 ⟨-k, by simpa using congrArg Neg.neg hk⟩⟩
        have sub : {z,-z} ⊆ T := Finset.insert_subset hz (Finset.singleton_subset_iff.mpr hnz)
        exact (show 2 = ∑ w ∈ {z,-z}, (if A ∈ C w then 1 else 0) by rw [Finset.sum_insert (by simpa using hd : z ∉ ({-z} : Finset _)), Finset.sum_singleton, ite_eq_left ha, ite_eq_left hna]).le.trans
          (Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        have sub : C z ⊆ U := fun A hA ↦ Finset.mem_biUnion.mpr ⟨z,hz,hA⟩
        simp [Finset.inter_eq_right.mpr sub]
  calc
    _ ≤ (∑ z ∈ T, (C z).card) * q^m := Nat.mul_le_mul_right _ twice
    _ = _ := Finset.sum_mul _ _ _
    _ ≤ ∑ _ ∈ T, q^(n*m) := Finset.sum_le_sum (fibre_bound e s R B hR he hs hq)
    _ = _ := by simp [T]

private theorem ball_card {ι : Type*} [Fintype ι] (j : ℕ) :
    (integerBall (ι := ι) (Real.sqrt j)).card = ballCount (Fintype.card ι) j - 1 := by
  classical
  let T := integerBall (ι := ι) (Real.sqrt j)
  have mem (z : ι → ℤ) : z ∈ T ↔ z ≠ 0 ∧ normSq z ≤ j := by
    rw [show T = _ from rfl, mem_integerBall (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
      ← real_sq]
    norm_cast
  have allmem (z : ι → ℤ) : z ∈ insert 0 T ↔ normSq z ≤ j := by
    rw [Finset.mem_insert, mem]
    by_cases h : z = 0 <;> simp [h, normSq]
  have ec := Nat.card_congr (Equiv.subtypeEquivRight allmem)
  have h0 : 0 ∉ T := fun h ↦ (mem 0 |>.mp h).1 rfl
  change Nat.card ↥(insert 0 T) = Nat.card (Points ι j) at ec
  rw [card_points, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_insert_of_notMem h0] at ec
  change T.card = _
  omega

/-- The uniform-design bound with its probability denominators cleared. -/
theorem design_bound (e : Fin m → ℤ) (s : Fin n → ℤ) (η j : ℕ)
    (he : ∀ i, (e i).natAbs ≤ η) (hs : ∀ i, (s i).natAbs ≤ η)
    (hq : j * (1+η^2) < q^2) :
    2 * (badMatrices q e s (Real.sqrt j)).card * q^m ≤
      (ballCount (m+n+1) j - 1) * q^(n*m) := by
  have conv (a : ℤ) (ha : a.natAbs ≤ η) : |(a : ℝ)| ≤ η := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast ha
  have hh : Real.sqrt j * Real.sqrt (1+(η : ℝ)^2) < q := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    exact_mod_cast hq
  simpa [ball_card, Coord, Nat.add_assoc] using
    pair_count e s _ η (Real.sqrt_nonneg j) (fun i ↦ conv _ (he i)) (fun i ↦ conv _ (hs i)) hh

private theorem normSq_smul {ι : Type*} [Fintype ι] (k : ℤ) (v : ι → ℤ) :
    normSq (k • v) = k.natAbs^2 * normSq v := by
  simp [normSq, Finset.mul_sum, Pi.smul_apply, Int.natAbs_mul, mul_pow]

theorem unique_pair (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (hA : A ∉ badMatrices q e s (Real.sqrt (normSq (plantedPoint e s))))
    (z : Coord m n → ℤ) (hz : member A e s z) (hne : z ≠ 0)
    (hle : normSq z ≤ normSq (plantedPoint e s)) :
    z = plantedPoint e s ∨ z = -plantedPoint e s := by
  classical
  let v := plantedPoint e s
  have hball : z ∈ integerBall (Real.sqrt (normSq v)) := by
    apply (mem_integerBall (Real.sqrt_nonneg _) _).mpr
    refine ⟨hne, ?_⟩
    rw [Real.sq_sqrt (by positivity), ← real_sq]
    exact_mod_cast hle
  have hm : ∃ k : ℤ, z = k • v := by
    by_contra hh
    exact hA (Finset.mem_biUnion.mpr ⟨z,hball,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,hh⟩⟩)
  obtain ⟨k,hk⟩ := hm
  have hv : 1 ≤ normSq v :=
    Finset.single_le_sum (f := fun i ↦ (v i).natAbs^2) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ (.inr (.inr ())))
  change normSq z ≤ normSq v at hle
  rw [hk,normSq_smul] at hle
  have h1 : k.natAbs^2 ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hle) (by omega)
  have hk1 : k.natAbs ≤ 1 := by nlinarith
  have hk0 : k ≠ 0 := by rintro rfl; simp_all
  have : k = 1 ∨ k = -1 := by omega
  rcases this with rfl | rfl <;> simp_all [v]

/-- At the plant radius the counted bad designs are exactly those admitting a competitor,
including a tie at the plant norm. -/
theorem mem_bad_iff_competitor (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) :
    A ∈ badMatrices q e s (Real.sqrt (normSq (plantedPoint e s))) ↔
      ∃ z, member A e s z ∧ z ≠ 0 ∧ z ≠ plantedPoint e s ∧ z ≠ -plantedPoint e s ∧
        normSq z ≤ normSq (plantedPoint e s) := by
  classical
  constructor
  · intro ha
    obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨hmem,hk⟩ := (Finset.mem_filter.mp hm).2
    obtain ⟨hne,hle⟩ := (mem_integerBall (Real.sqrt_nonneg _) z).mp hz
    rw [Real.sq_sqrt (by positivity), ← real_sq] at hle
    refine ⟨z,hmem,hne,fun h ↦ hk ⟨1, by simpa using h⟩,
      fun h ↦ hk ⟨-1, by simpa using h⟩, ?_⟩
    exact_mod_cast hle
  · rintro ⟨z,hz,hne,hp,hn,hle⟩
    by_contra hA
    exact (unique_pair e s A hA z hz hne hle).elim hp hn

/-- Uniform probability over the retained matrix, conditioned on the fixed planting. -/
theorem competitor_probability (e : Fin m → ℤ) (s : Fin n → ℤ) (η : ℕ)
    (he : ∀ i, (e i).natAbs ≤ η) (hs : ∀ j, (s j).natAbs ≤ η)
    (hq : normSq (plantedPoint e s) * (1+η^2) < q^2) :
    ((badMatrices q e s (Real.sqrt (normSq (plantedPoint e s)))).card : ℚ) / q^(n*m) ≤
      ((ballCount (m+n+1) (normSq (plantedPoint e s)) - 1 : ℕ) : ℚ) / (2*q^m) := by
  have hpos : (0 : ℚ) < q := by exact_mod_cast (Fact.out : Nat.Prime q).pos
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := design_bound e s η _ he hs hq
  rw [Nat.mul_comm 2 _, Nat.mul_assoc] at h
  exact_mod_cast h

theorem exact_svp_recovery (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (hA : A ∉ badMatrices q e s (Real.sqrt (normSq (plantedPoint e s))))
    (z : Coord m n → ℤ) (hz : member A e s z) (hne : z ≠ 0)
    (svp : ∀ w, member A e s w → w ≠ 0 → normSq z ≤ normSq w) :
    (z = plantedPoint e s ∨ z = -plantedPoint e s) ∧
      (fun i ↦ z (.inr (.inr ())) * z (.inr (.inl i))) = s := by
  have hv : plantedPoint e s ≠ 0 := fun h ↦ by
    have := congrFun h (.inr (.inr ()))
    norm_num [plantedPoint] at this
  have h := unique_pair e s A hA z hz hne (svp _ (SigabaNeo.LLL.member_planted A e s) hv)
  refine ⟨h, ?_⟩
  rcases h with rfl | rfl <;> ext <;> simp [plantedPoint]

end SigabaNeo.SampleDeletion

#print axioms SigabaNeo.SampleDeletion.mem_bad_iff_competitor
#print axioms SigabaNeo.SampleDeletion.competitor_probability
#print axioms SigabaNeo.SampleDeletion.design_bound
#print axioms SigabaNeo.SampleDeletion.unique_pair
#print axioms SigabaNeo.SampleDeletion.exact_svp_recovery

#print axioms SigabaNeo.SampleDeletion.prefix_member_iff
#print axioms SigabaNeo.SampleDeletion.prefix_design_card
