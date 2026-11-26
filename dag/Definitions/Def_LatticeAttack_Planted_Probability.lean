module

public import SigabaNeoStd.Lattices.QAry

set_option autoImplicit true

public section

namespace SigabaNeo.Planted

variable {m n q : ℕ} [Fact q.Prime]

abbrev Coord (m n : ℕ) := Fin m ⊕ (Fin n ⊕ Unit)

private abbrev last : Coord m n := .inr (.inr ())
private abbrev col (j : Fin n) : Coord m n := .inr (.inl j)

def plantedPoint (e : Fin m → ℤ) (s : Fin n → ℤ) : Coord m n → ℤ
  | .inl i => e i
  | .inr (.inl j) => s j
  | .inr (.inr ()) => 1

def member (A : Matrix (Fin m) (Fin n) (ZMod q)) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (z : Coord m n → ℤ) : Prop :=
  ∀ i, (z (.inl i) : ZMod q) + A i ⬝ᵥ (fun j ↦ (z (col j) : ZMod q)) =
    (z last : ZMod q) * (A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i)

private theorem coord_sq {ι : Type*} [Fintype ι] (z : ι → ℤ) (i : ι) :
    (z i : ℝ)^2 ≤ ∑ j, (z j : ℝ)^2 :=
  Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j : ℝ)) (Finset.mem_univ i)

noncomputable def integerBall {ι : Type*} [Fintype ι] (R : ℝ) : Finset (ι → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : ι ↦ Finset.Icc (-⌈R⌉) ⌈R⌉).filter
    (fun z ↦ z ≠ 0 ∧ ∑ j, (z j : ℝ)^2 ≤ R^2)

theorem mem_integerBall {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 ≤ R) (z : ι → ℤ) :
    z ∈ integerBall R ↔ z ≠ 0 ∧ ∑ j, (z j : ℝ)^2 ≤ R^2 := by
  classical
  unfold integerBall
  refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨?_, h⟩⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi := (coord_sq z i).trans h.2
  have hc := Int.le_ceil R
  constructor
  · exact_mod_cast (by nlinarith : -(⌈R⌉ : ℝ) ≤ (z i : ℝ))
  · exact_mod_cast (by nlinarith : (z i : ℝ) ≤ (⌈R⌉ : ℝ))

omit [Fact q.Prime] in
private theorem discrepancy {a b t : ℤ} {R B : ℝ} (hR : 0 ≤ R)
    (hab : (a : ℝ)^2 + (t : ℝ)^2 ≤ R^2) (hb : |(b : ℝ)| ≤ B)
    (hq : R * Real.sqrt (1 + B^2) < q) : |a - t*b| < (q : ℤ) := by
  have hbs := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have h := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 1 + (b : ℝ)^2)
  have h' := mul_le_mul_of_nonneg_right hbs (sq_nonneg R)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+B^2)
  have hm : |(a : ℝ) - t*b| ≤ R * Real.sqrt (1+B^2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, mul_pow, hs]
    nlinarith [sq_nonneg ((a : ℝ)*b + t)]
  exact_mod_cast hm.trans_lt hq

private theorem fibre_le (u : Fin n → ZMod q) (v : Fin m → ZMod q) (hu : u ≠ 0) :
    ((Finset.univ.filter fun A : Matrix (Fin m) (Fin n) (ZMod q) ↦ A.mulVec u = v).card *
      q^m) ≤ q^(n*m) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by contrapose! hu; ext i; exact hu i
  let S := {A : Matrix (Fin m) (Fin n) (ZMod q) // A.mulVec u = v}
  let f (p : S × (Fin m → ZMod q)) : Matrix (Fin m) (Fin n) (ZMod q) :=
    fun i k ↦ p.1.val i k + if k = j then p.2 i else 0
  have eval (p) (i) : (f p).mulVec u i = v i + p.2 i * u j := by
    have hi := congrFun p.1.property i
    change ∑ k : Fin n, (p.1.val i k + if k = j then p.2 i else 0) * u k = _
    simp [add_mul, Finset.sum_add_distrib, ite_mul, ← hi, Matrix.mulVec, dotProduct]
  have inj : Function.Injective f := by
    intro p r h
    have hx : p.2 = r.2 := by
      ext i
      have he := congrArg (fun A : Matrix _ _ _ ↦ A.mulVec u i) h
      rw [eval, eval] at he
      exact mul_right_cancel₀ hj (add_left_cancel he)
    refine Prod.ext (Subtype.ext ?_) hx
    ext i k
    exact add_right_cancel (by simpa only [f, hx] using congrFun (congrFun h i) k)
  have hc := Fintype.card_le_of_injective f inj
  change Fintype.card (S × (Fin m → ZMod q)) ≤ Fintype.card (Fin m → Fin n → ZMod q) at hc
  rw [Fintype.card_prod] at hc
  simp only [S, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul] at hc
  simpa [Fintype.card_subtype] using hc

noncomputable def badMatrices (q : ℕ) [Fact q.Prime] (e : Fin m → ℤ) (s : Fin n → ℤ)
    (R : ℝ) : Finset (Matrix (Fin m) (Fin n) (ZMod q)) := by
  classical
  exact (integerBall R).biUnion fun z ↦ Finset.univ.filter fun A ↦
    member A e s z ∧ ¬ ∃ k : ℤ, z = k • plantedPoint e s

/-- Uniform matrix probability, with both denominators cleared in the natural numbers. -/
theorem badMatrices_card (e : Fin m → ℤ) (s : Fin n → ℤ) (R B : ℝ) (hR : 0 ≤ R)
    (he : ∀ i, |(e i : ℝ)| ≤ B) (hs : ∀ j, |(s j : ℝ)| ≤ B)
    (hq : R * Real.sqrt (1+B^2) < q) :
    (badMatrices q e s R).card * q^m ≤
      (integerBall (ι := Coord m n) R).card * q^(n*m) := by
  classical
  let T := integerBall (ι := Coord m n) R
  let C (z : Coord m n → ℤ) := Finset.univ.filter fun A : Matrix (Fin m) (Fin n) (ZMod q) ↦
    member A e s z ∧ ¬ ∃ k : ℤ, z = k • plantedPoint e s
  change (T.biUnion C).card * _ ≤ _
  calc
    _ ≤ (∑ z ∈ T, (C z).card) * q^m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ z ∈ T, (C z).card * q^m := Finset.sum_mul _ _ _
    _ ≤ ∑ _ ∈ T, q^(n*m) := by
      apply Finset.sum_le_sum
      intro z hz
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
    _ = _ := by simp [T]

#print axioms badMatrices_card

end SigabaNeo.Planted
