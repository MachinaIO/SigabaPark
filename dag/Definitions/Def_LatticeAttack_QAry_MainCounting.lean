module

public import Definitions.Def_LatticeAttack_QAry_RankDefect

set_option autoImplicit true

/-! # Counting projected spatial rows and centering labelled partitions

The box estimate uses independent bounded integer vectors spanning the rational pivot space.
Its index factor is the order of the quotient by the congruence lattice. The centering
identity uses the same singleton mass in both terms, as holds for unrestricted grid pivots.
-/

public section
namespace SigabaNeo.QAry

open Finset
open scoped BigOperators

/-- The two choices for each remaining label after fixing the nonsingleton blocks. -/
theorem singletonChoices {ι : Type*} [DecidableEq ι] (s : Finset ι) (M : ℝ) :
    (∑ a ∈ s.powerset, M ^ a.card * (-M) ^ (s \ a).card) =
      if s = ∅ then 1 else 0 := by
  classical
  by_cases hs : s = ∅
  · simp [hs]
  simpa [hs, zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs))] using (Finset.prod_add (fun _ : ι ↦ M) (fun _ ↦ -M) s).symm

/-- Summing over all nonsingleton patterns leaves only those covering every label.
The coefficient includes block masses and any orientation multiplicities. -/
theorem centeredPartitionSum {ι κ : Type*} [DecidableEq ι] (patterns : Finset κ)
    (labels : Finset ι) (covered : κ → Finset ι) (mass : κ → ℝ) (M : ℝ) :
    (∑ p ∈ patterns, mass p * ∑ a ∈ (labels \ covered p).powerset,
      M ^ a.card * (-M) ^ ((labels \ covered p) \ a).card) =
      ∑ p ∈ patterns with labels ⊆ covered p, mass p := by
  classical
  simp_rw [singletonChoices]
  simp [Finset.sum_filter, Finset.sdiff_eq_empty_iff_subset, mul_ite]

private def pivotBox (t B : ℕ) : Finset (Fin t → ℤ) :=
  Fintype.piFinset fun _ ↦ Icc (-(B : ℤ)) (B : ℤ)

private theorem mem_pivotBox {t B : ℕ} {x : Fin t → ℤ} :
    x ∈ pivotBox t B ↔ ∀ i, |x i| ≤ (B : ℤ) := by
  simp [pivotBox, Fintype.mem_piFinset, abs_le]

/-- Each congruence class has a small representative by rounding coordinates in the
rational basis supplied by independent spatial rows of a contributing array. -/
theorem boundedCosetRepresentative {t B : ℕ} (L : AddSubgroup (Fin t → ℤ))
    (v : Fin t → Fin t → ℤ) (hv : ∀ j, v j ∈ L)
    (basis : Module.Basis (Fin t) ℚ (Fin t → ℚ))
    (hb : ∀ j i, basis j i = (v j i : ℚ)) (bound : ∀ j i, |v j i| ≤ (B : ℤ))
    (c : (Fin t → ℤ) ⧸ L) :
    ∃ y : Fin t → ℤ, (y : (Fin t → ℤ) ⧸ L) = c ∧ ∀ i, |y i| ≤ ((t * B : ℕ) : ℤ) := by
  induction c using QuotientAddGroup.induction_on with
  | _ x =>
    let z : Fin t → ℚ := fun i ↦ x i
    let a := basis.repr z
    let w : Fin t → ℤ := ∑ j, ⌊a j⌋ • v j
    refine ⟨x - w, ?_, ?_⟩
    · have hw : w ∈ L := L.sum_mem fun j _ ↦ L.zsmul_mem (hv j) _
      simp [QuotientAddGroup.mk_sub, (QuotientAddGroup.eq_zero_iff _).mpr hw]
    · intro i
      have he := congrFun (basis.sum_repr z) i
      change (∑ j, a j • basis j) i = z i at he
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hb] at he
      have hy : (((x-w) i : ℤ) : ℚ) = ∑ j, (a j - ⌊a j⌋) * (v j i : ℚ) := by
        rw [show (∑ j, (a j - ⌊a j⌋) * (v j i : ℚ)) = _ from
          Finset.sum_congr rfl (fun j _ ↦ sub_mul _ _ _), sum_sub_distrib, he]
        simp [w, z, Finset.sum_apply]
      have hj (j) : |(a j - ⌊a j⌋) * (v j i : ℚ)| ≤ B := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
        apply (mul_le_of_le_one_left (abs_nonneg _) (by linarith [Int.lt_floor_add_one (a j)])).trans
        exact_mod_cast bound j i
      have hs := (Finset.abs_sum_le_sum_abs _ univ).trans (Finset.sum_le_sum (s := univ) fun j _ ↦ hj j)
      rw [← hy] at hs
      exact_mod_cast (by simpa using hs : |(((x-w) i : ℤ) : ℚ)| ≤ (t : ℚ)*B)

/-- Count points by translating them once per congruence class. Distinct pairs have
distinct translates, all in the box of radius (t+1)B. -/
theorem projectedBoxCount {t B : ℕ} (L : AddSubgroup (Fin t → ℤ))
    [Fintype ((Fin t → ℤ) ⧸ L)] [DecidablePred (· ∈ L)]
    (v : Fin t → Fin t → ℤ) (hv : ∀ j, v j ∈ L)
    (basis : Module.Basis (Fin t) ℚ (Fin t → ℚ))
    (hb : ∀ j i, basis j i = (v j i : ℚ)) (bound : ∀ j i, |v j i| ≤ (B : ℤ)) :
    ((Fintype.piFinset fun _ : Fin t ↦ Icc (-(B : ℤ)) (B : ℤ)).filter (· ∈ L)).card *
      Fintype.card ((Fin t → ℤ) ⧸ L) ≤ (2*((t+1)*B)+1)^t := by
  classical
  let S := (pivotBox t B).filter (· ∈ L)
  choose y hy hbound using boundedCosetRepresentative L v hv basis hb bound
  let f (p : S × ((Fin t → ℤ) ⧸ L)) : pivotBox t ((t+1)*B) :=
    ⟨p.1.val + y p.2, mem_pivotBox.mpr fun i ↦ by
      have hx := mem_pivotBox.mp (mem_filter.mp p.1.property).1 i
      have hh := abs_add_le (p.1.val i) (y p.2 i)
      push_cast at *
      change |p.1.val i + y p.2 i| ≤ _
      have hbi := hbound p.2 i
      nlinarith⟩
  have hf : Function.Injective f := by
    rintro ⟨x,c⟩ ⟨x',c'⟩ h
    have he : x.val + y c = x'.val + y c' := congrArg Subtype.val h
    have hc := congrArg (QuotientAddGroup.mk' L) he
    have hx := (QuotientAddGroup.eq_zero_iff _).mpr (mem_filter.mp x.property).2
    have hx' := (QuotientAddGroup.eq_zero_iff _).mpr (mem_filter.mp x'.property).2
    simp only [map_add, QuotientAddGroup.mk'_apply, hx, hx', zero_add, hy] at hc
    subst c'
    exact Prod.ext (Subtype.ext (add_right_cancel he)) rfl
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe] at hc
  have box_card (b : ℕ) : (pivotBox t b).card = (2*b+1)^t := by
    have hi : (Icc (-(b : ℤ)) (b : ℤ)).card = 2*b+1 := by rw [Int.card_Icc]; omega
    simp [pivotBox, Fintype.card_piFinset, hi]
  rwa [box_card] at hc

open Classical in
/-- Fixed projected residue space. Each spatial row loses a factor of q for each
missing residue dimension. The basis is supplied by the contributing array. -/
theorem residueBoxCount {q t B : ℕ} [Fact q.Prime]
    (U : Submodule (ZMod q) (Fin t → ZMod q))
    (v : Fin t → Fin t → ℤ) (hv : ∀ j, (fun i ↦ (v j i : ZMod q)) ∈ U)
    (basis : Module.Basis (Fin t) ℚ (Fin t → ℚ))
    (hb : ∀ j i, basis j i = (v j i : ℚ)) (bound : ∀ j i, |v j i| ≤ (B : ℤ)) :
    ((Fintype.piFinset fun _ : Fin t ↦ Icc (-(B : ℤ)) (B : ℤ)).filter
      (fun x ↦ (fun i ↦ (x i : ZMod q)) ∈ U)).card *
      q^(t - Module.finrank (ZMod q) U) ≤ (2*((t+1)*B)+1)^t := by
  classical
  let f : (Fin t → ℤ) →+ ((Fin t → ZMod q) ⧸ U) :=
    U.mkQ.toAddMonoidHom.comp <| AddMonoidHom.pi fun i ↦
      (Int.castAddHom (ZMod q)).comp (Pi.evalAddMonoidHom _ i)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := U.mkQ_surjective y
    refine ⟨fun i ↦ (x i).val, congrArg U.mkQ ?_⟩
    ext i
    simp
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  let := Fintype.ofEquiv _ e.symm.toEquiv
  have hmem (x : Fin t → ℤ) : x ∈ f.ker ↔ (fun i ↦ (x i : ZMod q)) ∈ U :=
    Submodule.Quotient.mk_eq_zero U
  have h := projectedBoxCount f.ker v (fun j ↦ (hmem _).mpr (hv j)) basis hb bound
  have hd := U.finrank_quotient_add_finrank
  simp at hd
  have hr : Module.finrank (ZMod q) ((Fin t → ZMod q) ⧸ U) =
      t - Module.finrank (ZMod q) U := by omega
  rw [Fintype.card_congr e.toEquiv, Module.card_eq_pow_finrank (K := ZMod q), ZMod.card, hr] at h
  simpa only [hmem] using h

/-- Q2 for the projected arrays. Every array has t rationally independent spatial rows,
and the reductions of all its spatial rows lie in the span of at most u generators.
The factor for enumerating all generator lists is charged only once per array. -/
theorem projectedArraysCount {q m t u B : ℕ} [Fact q.Prime]
    (S : Finset (Fin m → Fin t → ℤ))
    (bound : ∀ X ∈ S, ∀ j i, |X j i| ≤ (B : ℤ))
    (spans : ∀ X ∈ S, ∃ r : Fin t → Fin m,
      LinearIndependent ℚ (fun j i ↦ (X (r j) i : ℚ)))
    (res : ∀ X ∈ S, ∃ g : Fin u → Fin t → ZMod q,
      ∀ j, (fun i ↦ (X j i : ZMod q)) ∈ Submodule.span (ZMod q) (Set.range g)) :
    S.card * (q^(t-u))^m ≤ (q^t)^u * ((2*((t+1)*B)+1)^t)^m := by
  classical
  let U (g : Fin u → Fin t → ZMod q) := Submodule.span (ZMod q) (Set.range g)
  let F (g : Fin u → Fin t → ZMod q) := S.filter fun X ↦
    ∀ j, (fun i ↦ (X j i : ZMod q)) ∈ U g
  have each (g) : (F g).card * (q^(t-u))^m ≤ ((2*((t+1)*B)+1)^t)^m := by
    by_cases hn : (F g).Nonempty
    · obtain ⟨X, hX⟩ := hn
      obtain ⟨hs, hx⟩ := mem_filter.mp hX
      obtain ⟨r, hr⟩ := spans X hs
      let v := fun j ↦ X (r j)
      let basis := basisOfPiSpaceOfLinearIndependent hr
      have hb (j i) : basis j i = (v j i : ℚ) := by
        change (⇑(basisOfPiSpaceOfLinearIndependent hr)) j i = _
        rw [coe_basisOfPiSpaceOfLinearIndependent]
      have h := residueBoxCount (U g) v (fun j ↦ hx (r j)) basis hb
        (fun j i ↦ bound X hs (r j) i)
      let T := (pivotBox t B).filter fun x ↦ (fun i ↦ (x i : ZMod q)) ∈ U g
      have hd : Module.finrank (ZMod q) (U g) ≤ u := by
        simpa [U, Set.finrank] using (finrank_range_le_card (R := ZMod q) g)
      have ht : T.card * q^(t-u) ≤ (2*((t+1)*B)+1)^t :=
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Fact.out : q.Prime).pos
          (Nat.sub_le_sub_left hd t))).trans h
      have sub : F g ⊆ Fintype.piFinset (fun _ : Fin m ↦ T) := by
        intro Y hY
        obtain ⟨hs, hy⟩ := mem_filter.mp hY
        exact Fintype.mem_piFinset.mpr fun j ↦ mem_filter.mpr
          ⟨mem_pivotBox.mpr (bound Y hs j), hy j⟩
      have hcard : (F g).card ≤ T.card^m := by
        simpa [Fintype.card_piFinset] using card_le_card sub
      exact (Nat.mul_le_mul_right _ hcard).trans
        (by simpa [mul_pow] using Nat.pow_le_pow_left ht m)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have cover : S ⊆ univ.biUnion F := by
    intro X hX
    obtain ⟨g, hg⟩ := res X hX
    exact mem_biUnion.mpr ⟨g, mem_univ _, mem_filter.mpr ⟨hX, hg⟩⟩
  calc
    _ ≤ (∑ g, (F g).card) * (q^(t-u))^m :=
      Nat.mul_le_mul_right _ ((card_le_card cover).trans card_biUnion_le)
    _ = ∑ g, (F g).card * (q^(t-u))^m := sum_mul ..
    _ ≤ ∑ _ : Fin u → Fin t → ZMod q, ((2*((t+1)*B)+1)^t)^m :=
      sum_le_sum fun g _ ↦ each g
    _ = _ := by simp [ZMod.card, Fintype.card_pi]

/-- Select a spanning independent subfamily of row values indexed by the rank. -/
private theorem pivotRows {K : Type*} [Field K] {m t d : ℕ}
    (X : Matrix (Fin m) (Fin t) K) (hd : X.rank = d) :
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

/-- Multiplicity of the full rational-rank stratum in a fixed pivot projection,
with the modular rank read directly from each projected matrix. -/
theorem projectedRankStratum {q m t u B : ℕ} [Fact q.Prime]
    (S : Finset (Matrix (Fin m) (Fin t) ℤ))
    (bound : ∀ X ∈ S, ∀ j i, |X j i| ≤ (B : ℤ))
    (rat : ∀ X ∈ S, (X.map (Int.castRingHom ℚ)).rank = t)
    (modRank : ∀ X ∈ S, (X.map (Int.castRingHom (ZMod q))).rank = u) :
    S.card * (q^(t-u))^m ≤ (q^t)^u * ((2*((t+1)*B)+1)^t)^m := by
  apply projectedArraysCount S bound
  · intro X hX
    obtain ⟨r, hr, _⟩ := pivotRows _ (rat X hX)
    exact ⟨r, hr⟩
  · intro X hX
    let Y := Matrix.map (show Matrix (Fin m) (Fin t) ℤ from X) (Int.castRingHom (ZMod q))
    obtain ⟨r, _, hr⟩ := pivotRows Y (modRank X hX)
    refine ⟨Y.row ∘ r, fun j ↦ ?_⟩
    rw [hr]
    exact Submodule.subset_span ⟨j, rfl⟩

#print axioms projectedRankStratum
#print axioms projectedArraysCount
#print axioms residueBoxCount
#print axioms singletonChoices
#print axioms centeredPartitionSum
#print axioms boundedCosetRepresentative
#print axioms projectedBoxCount

end SigabaNeo.QAry
