module

public import Definitions.Def_LatticeAttack_QAry_MainCounting

set_option autoImplicit true

/-! # Bounded rational row spaces and the cost of dependent pivot arrays

All counts are finite. There are no continuum or integration hypotheses.
-/

public section
namespace SigabaNeo.QAry

open Finset

abbrev rationalRows {m k : ℕ} (X : Matrix (Fin m) (Fin k) ℤ) :=
  Submodule.span ℚ (Set.range (X.map (Int.castRingHom ℚ)).row)

private theorem selectRows {K : Type*} [Field K] {m k d : ℕ} (X : Matrix (Fin m) (Fin k) K)
    (hd : X.rank = d) :
    ∃ r : Fin d → Fin m, LinearIndependent K (X.row ∘ r) ∧
      Submodule.span K (Set.range (X.row ∘ r)) = Submodule.span K (Set.range X.row) := by
  classical
  obtain ⟨T, f, hf, hs, hi⟩ := exists_linearIndependent' K X.row
  let : Finite T := Finite.of_injective f hf
  let := Fintype.ofFinite T
  have h : Fintype.card T = d := by
    rw [← hd, Matrix.rank_eq_finrank_span_row, ← hs, finrank_span_eq_card hi]
  let e := (Fintype.equivFinOfCardEq h).symm
  refine ⟨f ∘ e, hi.comp e e.injective, ?_⟩
  change Submodule.span K (Set.range ((X.row ∘ f) ∘ e)) = _
  rwa [Set.range_comp, e.surjective.range_eq, Set.image_univ]

private abbrev Box (B : ℕ) := ↥(Icc (-(B : ℤ)) (B : ℤ))

private theorem card_box (B : ℕ) : Fintype.card (Box B) = 2 * B + 1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  omega

open Classical in
theorem rationalRowSpaceCount {m k d B : ℕ} (S : Finset (Matrix (Fin m) (Fin k) ℤ))
    (bound : ∀ X ∈ S, ∀ i j, |X i j| ≤ (B : ℤ))
    (rank : ∀ X ∈ S, (X.map (Int.castRingHom ℚ)).rank = d) :
    (S.image rationalRows).card ≤ ((2 * B + 1)^k)^d := by
  classical
  let space (v : Fin d → Fin k → Box B) :=
    Submodule.span ℚ (Set.range fun i j ↦ ((v i j : ℤ) : ℚ))
  have h : S.image rationalRows ⊆ univ.image space := by
    rintro W hW
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hW
    obtain ⟨r, _, hr⟩ := selectRows _ (rank X hX)
    exact mem_image.mpr ⟨fun i j ↦ ⟨X (r i) j, mem_Icc.mpr (abs_le.mp (bound X hX _ _))⟩,
      mem_univ _, hr⟩
  simpa only [card_univ, Fintype.card_pi, Finset.prod_const, Fintype.card_fin, card_box] using (card_le_card h).trans card_image_le

/-- A single coordinate projection works for every spatial row in a fixed row space. -/
theorem rationalRowPivots {m k d : ℕ} (X : Matrix (Fin m) (Fin k) ℤ)
    (hd : (X.map (Int.castRingHom ℚ)).rank = d) :
    ∃ c : Fin d → Fin k, Set.InjOn (fun x : Fin k → ℚ ↦ x ∘ c) (rationalRows X) := by
  obtain ⟨r, hi, hs⟩ := selectRows _ hd
  let V := (X.map (Int.castRingHom ℚ)).submatrix r id
  have hv : V.rank = d := by simpa using (LinearIndependent.rank_matrix (M := V) hi)
  obtain ⟨c, hc, _⟩ := selectRows V.transpose (by rw [Matrix.rank_transpose, hv])
  let P := V.submatrix id c
  have hc' : LinearIndependent ℚ P.col := hc
  have hp : Function.Injective P.vecMul := Matrix.vecMul_injective_iff.mpr
    (Matrix.linearIndependent_row_iff_isUnit.mpr (Matrix.linearIndependent_col_iff_isUnit.mp hc'))
  refine ⟨c, ?_⟩
  unfold rationalRows
  rw [← hs]
  change Set.InjOn (fun x : Fin k → ℚ ↦ x ∘ c) (Submodule.span ℚ (Set.range V.row))
  rw [← range_vecMulLinear]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  exact congrArg V.vecMulLinear (hp (show P.vecMul a = P.vecMul b from hab))

open Classical in
/-- Counting dependent arrays of each rational rank before applying the full-rank weight. -/
theorem rationalRankStratumCount {m k d B : ℕ} (S : Finset (Matrix (Fin m) (Fin k) ℤ))
    (bound : ∀ X ∈ S, ∀ i j, |X i j| ≤ (B : ℤ))
    (rank : ∀ X ∈ S, (X.map (Int.castRingHom ℚ)).rank = d) :
    S.card ≤ ((2 * B + 1)^k)^d * ((2 * B + 1)^d)^m := by
  classical
  have each (W) (hW : W ∈ S.image rationalRows) :
      (S.filter (fun X ↦ rationalRows X = W)).card ≤ ((2 * B + 1)^d)^m := by
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hW
    obtain ⟨c, hc⟩ := rationalRowPivots X (rank X hX)
    let T := S.filter (fun Y ↦ rationalRows Y = rationalRows X)
    let f (Y : T) (i : Fin m) (j : Fin d) : Box B :=
      ⟨Y.val i (c j), mem_Icc.mpr (abs_le.mp (bound _ (mem_filter.mp Y.property).1 _ _))⟩
    have mem (Y : T) (i : Fin m) :
        (Y.val.map (Int.castRingHom ℚ)).row i ∈ rationalRows X := by
      rw [← (mem_filter.mp Y.property).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    have inj : Function.Injective f := by
      intro Y Z h
      apply Subtype.ext
      ext i j
      have he := hc (mem Y i) (mem Z i) (by
        funext l
        exact congrArg (fun b : Box B ↦ ((b : ℤ) : ℚ)) (congrFun (congrFun h i) l))
      have hh : ((Y.val i j : ℤ) : ℚ) = ((Z.val i j : ℤ) : ℚ) := congrFun he j
      exact_mod_cast hh
    have h := Fintype.card_le_of_injective f inj
    rw [Fintype.card_coe] at h
    simpa only [Fintype.card_pi, Finset.prod_const, card_univ, Fintype.card_fin, card_box, T] using h
  calc
    _ = ∑ W ∈ S.image rationalRows, (S.filter (fun X ↦ rationalRows X = W)).card :=
      card_eq_sum_card_fiberwise fun _ ↦ mem_image_of_mem _
    _ ≤ ∑ _W ∈ S.image rationalRows, ((2 * B + 1)^d)^m := sum_le_sum each
    _ ≤ _ := by
      simpa using Nat.mul_le_mul_right (((2 * B + 1)^d)^m)
        (rationalRowSpaceCount S bound rank)

open Classical in
/-- Modular rank loss before projection. The modular pivot columns may themselves
lose rank, so the projected residue rows are merely spanned by u generators. -/
theorem modularRankStratumCount {q m k t u B : ℕ} [Fact q.Prime]
    (S : Finset (Matrix (Fin m) (Fin k) ℤ))
    (bound : ∀ X ∈ S, ∀ i j, |X i j| ≤ (B : ℤ))
    (rat : ∀ X ∈ S, (X.map (Int.castRingHom ℚ)).rank = t)
    (res : ∀ X ∈ S, (X.map (Int.castRingHom (ZMod q))).rank = u) :
    S.card * (q^(t-u))^m ≤
      ((2*B+1)^k)^t * ((q^t)^u * ((2*((t+1)*B)+1)^t)^m) := by
  classical
  let F W := S.filter fun X ↦ rationalRows X = W
  have each (W) (hW : W ∈ S.image rationalRows) :
      (F W).card * (q^(t-u))^m ≤ (q^t)^u * ((2*((t+1)*B)+1)^t)^m := by
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hW
    obtain ⟨c, hc⟩ := rationalRowPivots X (rat X hX)
    let project (Y : Matrix (Fin m) (Fin k) ℤ) := Y.submatrix id c
    let T := F (rationalRows X)
    have mem {Y} (h : Y ∈ T) (i : Fin m) :
        (Y.map (Int.castRingHom ℚ)).row i ∈ rationalRows X := by
      rw [← (mem_filter.mp h).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    have inj : Set.InjOn project T := by
      intro Y hY Z hZ he
      ext i j
      have e := hc (mem hY i) (mem hZ i) (by
        funext l
        exact congrArg (fun P : Matrix (Fin m) (Fin t) ℤ ↦ (P i l : ℚ)) he)
      exact_mod_cast (show (Y i j : ℚ) = (Z i j : ℚ) from congrFun e j)
    rw [← show (T.image project).card = T.card from card_image_of_injOn inj]
    apply projectedArraysCount
    · intro P h
      obtain ⟨Y, hY, rfl⟩ := mem_image.mp h
      exact fun i j ↦ bound Y (mem_filter.mp hY).1 i (c j)
    · intro P h
      obtain ⟨Y, hY, rfl⟩ := mem_image.mp h
      obtain ⟨r, hi, hs⟩ := selectRows _ (rat Y (mem_filter.mp hY).1)
      refine ⟨r, hi.map_injOn (LinearMap.funLeft ℚ ℚ c) ?_⟩
      rw [hs]
      change Set.InjOn (fun x : Fin k → ℚ ↦ x ∘ c) (rationalRows Y)
      rwa [(mem_filter.mp hY).2]
    · intro P h
      obtain ⟨Y, hY, rfl⟩ := mem_image.mp h
      let A := Y.map (Int.castRingHom (ZMod q))
      obtain ⟨r, _, hr⟩ := selectRows A (res Y (mem_filter.mp hY).1)
      let f := LinearMap.funLeft (ZMod q) (ZMod q) c
      refine ⟨f ∘ (A.row ∘ r), fun i ↦ ?_⟩
      rw [Set.range_comp f, ← Submodule.map_span, hr]
      exact ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  have hsum : S.card = ∑ W ∈ S.image rationalRows, (F W).card :=
    card_eq_sum_card_fiberwise fun _ ↦ mem_image_of_mem _
  rw [hsum, sum_mul]
  exact (sum_le_sum each).trans (by
    simpa using Nat.mul_le_mul_right ((q^t)^u * ((2*((t+1)*B)+1)^t)^m)
      (rationalRowSpaceCount S bound rat))

#print axioms modularRankStratumCount

open Classical in
/-- Freeing the pivots adds precisely the deficient-rank arrays. The same original
normalization is used on both sides, including on every deficient stratum. -/
theorem freeingPivotError {m k B : ℕ} (S : Finset (Matrix (Fin m) (Fin k) ℤ))
    (bound : ∀ X ∈ S, ∀ i j, |X i j| ≤ (B : ℤ))
    (w : Matrix (Fin m) (Fin k) ℤ → ℝ) (E scale : ℝ) (hs : 0 ≤ scale)
    (hE : 0 ≤ E) (hw : ∀ X ∈ S, |w X| ≤ E) :
    |(∑ X ∈ S, w X) / scale^(k*m) -
      (∑ X ∈ S with (X.map (Int.castRingHom ℚ)).rank = k, w X) / scale^(k*m)| ≤
      (∑ d ∈ range k, ((((2*B+1)^k)^d * ((2*B+1)^d)^m : ℕ) : ℝ) * E) /
        scale^(k*m) := by
  classical
  let r (X : Matrix (Fin m) (Fin k) ℤ) := (X.map (Int.castRingHom ℚ)).rank
  let D := S.filter fun X ↦ r X ≠ k
  have split : (∑ X ∈ S, w X) - (∑ X ∈ S with r X = k, w X) = ∑ X ∈ D, w X := by
    have h := sum_filter_add_sum_filter_not S (fun X ↦ r X = k) w
    dsimp [D]
    linarith
  rw [← sub_div, abs_div, abs_of_nonneg (pow_nonneg hs _), split]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hs _)
  have hm : (D : Set _).MapsTo r (range k) := by
    intro X hX
    exact mem_range.mpr (lt_of_le_of_ne
      (by simpa [r] using (X.map (Int.castRingHom ℚ)).rank_le_width) (mem_filter.mp hX).2)
  apply (abs_sum_le_sum_abs _ _).trans
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_le_sum
  intro d _
  let T := D.filter fun X ↦ r X = d
  have sub {X} (h : X ∈ T) : X ∈ S := (mem_filter.mp (mem_filter.mp h).1).1
  have hc := rationalRankStratumCount T (fun X h ↦ bound X (sub h))
    (fun _ h ↦ (mem_filter.mp h).2)
  calc
    _ ≤ ∑ _X ∈ T, E := sum_le_sum fun X h ↦ hw X (sub h)
    _ = (T.card : ℝ) * E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hE

#print axioms freeingPivotError
#print axioms rationalRowSpaceCount
#print axioms rationalRowPivots
#print axioms rationalRankStratumCount

end SigabaNeo.QAry
