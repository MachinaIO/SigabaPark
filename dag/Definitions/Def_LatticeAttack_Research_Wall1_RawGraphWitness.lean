import Definitions.Def_LatticeAttack_Research_Wall1_LongWinnerRawTail

set_option autoImplicit true

/-! Forward realization of integer graph witnesses through the physical restart. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Finset ControlledPlane TerminalProjection TerminalProjection.Restart506
open TerminalProjection.ChainState DualExit QaryMembership Submodule WithLp
open scoped Classical Matrix

private def shift {n d} (S : ChainState n (CoordSpace d)) (b : Fin 400 → ℤ) :=
  ∑ i, b i • S.g i

private def compatible (h : History) {t} (o : Fin 400 → ℤ) (v : Fin t → ℤ)
    (b : Fin 400 → ℤ) : Prop :=
  ∀ i, (o i : ZMod 3329) = b i + ∑ j, (v j : ZMod 3329) * past h j.val i

private def realizes (h : History) (t : ℕ) {n d} (S : ChainState n (CoordSpace d)) : Prop :=
  ∀ o (v : Fin t → ℤ) b, compatible h o v b →
    ∃ w ∈ S.M, ‖w + shift S b‖^2 ≤ sqLength o + sqLength v

private lemma initial_realizes (h : History) : realizes h 0 initial := by
  intro o v b hc
  let w := ∑ i, (o i - b i) • initial.g i
  have mem (i : Fin 400) : (o i - b i) • initial.g i ∈ initial.M := by
    have eqz : ((o i - b i : ℤ) : ZMod 3329) = 0 := by simpa using sub_eq_zero.mpr (by
      simpa [compatible] using hc i : (o i : ZMod 3329) = b i)
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp eqz
    rw [hk, mul_comm, mul_smul]
    exact initial.M.smul_mem k (by exact_mod_cast initial.periods i)
  refine ⟨w, initial.M.sum_mem (fun i _ ↦ mem i), ?_⟩
  have eq : w + shift initial b = ∑ i, o i • initial.g i := by
    simp [w, shift, sub_smul, sum_sub_distrib]
  rw [eq, EuclideanSpace.real_norm_sq_eq]
  simp [initial, sqLength, EuclideanSpace.basisFun_apply, ← Int.cast_smul_eq_zsmul ℝ,
    Pi.single_apply, mul_ite]

private lemma append_realizes {n d t} {h : History} {S : ChainState n (CoordSpace d)}
    (hr : realizes h t S) (o : Fin 400 → ℤ) (v : Fin (t+1) → ℤ) (b : Fin 400 → ℤ)
    (hc : compatible h o v b) :
    let W := incoming S (past h t)
    ∃ w ∈ W.M, ‖w + shift W b‖^2 ≤ sqLength o + sqLength v ∧
      (v (Fin.last t) ≠ 0 → w + shift W b ≠ 0) := by
  let k := v (Fin.last t)
  let c := past h t
  let b' (i : Fin 400) := b i + k * (c i).val
  have comp : compatible h o (fun j ↦ v j.castSucc) b' := by
    intro i
    rw [hc i, Fin.sum_univ_castSucc]
    simp [b', k, c, add_assoc, add_comm]
  obtain ⟨w, hw, hnorm⟩ := hr _ _ _ comp
  let e := windowCoord d
  let u := columnLift S.g c
  let a : WindowSpace (CoordSpace d) := toLp 2 (w + k • u, (k:ℝ))
  have ha : a ∈ (S.append c).M := by
    apply (mem_append_at_height S.M u a k rfl).2
    change S.M.mkQ (w + k • u) = _
    have zw : S.M.mkQ w = 0 := (Quotient.mk_eq_zero S.M).2 hw
    rw [map_add, map_zsmul, zw, zero_add]
  have shiftEq : shift (incoming S c) b = e (horizontalInclusion (shift S b)) := by
    simp only [shift, map_sum, map_zsmul]
    rfl
  have add : shift S b' = shift S b + k • u := by
    simp only [b', shift, add_smul, sum_add_distrib, u, columnLift, Finset.smul_sum,
      mul_smul, natCast_zsmul]
  refine ⟨e a, (show e.symm (e a) ∈ (S.append c).M by rwa [e.symm_apply_apply]), ?_, ?_⟩
  · rw [shiftEq, ← map_add, e.norm_map, WithLp.prod_norm_sq_eq_of_L2]
    change ‖w + k • u + shift S b‖^2 + ‖(k:ℝ) + 0‖^2 ≤ _
    rw [show w + k • u + shift S b = w + shift S b' by rw [add]; abel, add_zero,
      Real.norm_eq_abs, sq_abs]
    unfold sqLength
    conv_rhs => rhs; rw [Fin.sum_univ_castSucc]
    unfold sqLength at hnorm
    dsimp only [k]
    linarith only [hnorm]
  · intro hk he
    rw [shiftEq, ← map_add] at he
    have he := e.injective (he.trans (map_zero e).symm)
    have hh := congrArg (fun x : WindowSpace (CoordSpace d) ↦ x.snd) he
    change (k:ℝ) + 0 = 0 at hh
    exact hk (by exact_mod_cast (by simpa using hh : (k:ℝ) = 0))

private lemma incoming_realizes {n d t} {h : History} {S : ChainState n (CoordSpace d)}
    (hr : realizes h t S) : realizes h (t+1) (incoming S (past h t)) := by
  intro o v b hc
  obtain ⟨w,hw,hn,_⟩ := append_realizes hr o v b hc
  exact ⟨w,hw,hn⟩

private lemma graph_realizes (h : History) (t : ℕ) : realizes h t (graphPrefix h t) := by
  induction t with
  | zero => exact initial_realizes h
  | succ t ih => exact incoming_realizes ih

private lemma freeze_realizes {n d t} {h : History} {S : ChainState n (CoordSpace (d+1))}
    (hr : realizes h t S) : realizes h t S.freeze := by
  intro o v b hc
  obtain ⟨w,hw,hn⟩ := hr o v b hc
  let K := (ℝ ∙ S.winner)ᗮ
  let e := coord (d := d) (V := K) (by
    have hh := (ℝ ∙ S.winner).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton S.shortest.2.1, finrank_euclideanSpace_fin] at hh
    change 1 + Module.finrank ℝ K = d+1 at hh
    omega)
  let L := K.orthogonalProjectionOnto
  refine ⟨e (L w), ?_, ?_⟩
  · change e.symm (e (L w)) ∈ projectedModule S.M K
    rw [e.symm_apply_apply]
    exact ⟨w,hw,rfl⟩
  · have H : shift S.freeze b = e (L (shift S b)) := by
      simp only [shift, map_sum, map_zsmul]
      rfl
    rw [H, ← map_add, ← map_add, e.norm_map]
    exact (pow_le_pow_left₀ (norm_nonneg _) (K.norm_orthogonalProjectionOnto_apply_le _) 2).trans hn

private lemma retained_realizes (h : History) (j : ℕ) : realizes h (105+j) (retained h j) := by
  induction j with
  | zero => exact graph_realizes h 105
  | succ j ih => exact freeze_realizes (incoming_realizes ih)

/-- Every short raw prefix graph vector with nonzero newest coordinate survives in the
current window, even when all earlier projections depend on the matrix. -/
theorem winner_le_of_raw_vector (A : Sample) {j : ℕ} (hj : j < 406) {r : ℝ} (hr : 0 ≤ r)
    (o : Fin 400 → ℤ) (v : Fin ((105+j)+1) → ℤ) (hv : v (Fin.last (105+j)) ≠ 0)
    (hc : designPrefix (by omega : (105+j)+1 ≤ 512) A *ᵥ reduce 3329 v = reduce 3329 o)
    (hs : sqLength o + sqLength v ≤ r^2) : s j A ≤ r := by
  have comp : compatible (history A) o v 0 := by
    intro i
    rw [Pi.zero_apply, Int.cast_zero, zero_add]
    have eqn := congrFun hc i
    change (∑ k, A i (k.castLE (by omega)) * (v k : ZMod 3329)) = (o i : ZMod 3329) at eqn
    rw [← eqn]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [past, dite_eq_left (show k.val < 511 by omega), history]
    rw [mul_comm]
    rfl
  obtain ⟨w,hw,hn,hne⟩ := append_realizes (retained_realizes (history A) j) o v 0 comp
  simp only [shift, Pi.zero_apply, zero_smul, sum_const_zero, add_zero] at hn hne
  have hmin := (window (history A) j).shortest.2.2 w hw (hne hv)
  have eqn : s j A = ‖(window (history A) j).winner‖ := by
    change ‖(window (history A) (min j 405)).winner‖ = _
    rw [min_eq_left (by omega)]
  rw [eqn]
  exact hmin.trans ((sq_le_sq₀ (norm_nonneg _) hr).mp (hn.trans hs))

/-- A short raw affine-coset witness remains a short representative in the actual
retained quotient after all preceding selected projections. Unlike a shortest-vector
witness, a coset representative may be zero and needs no nonzero newest coordinate. -/
theorem retained_coset_representative (A : Sample) {j : ℕ} (hj : j ≤ 406)
    (o : Fin 400 → ℤ) (v : Fin (105+j) → ℤ) (b : Fin 400 → ℤ)
    (hc : ∀ i, (o i : ZMod 3329) = (b i : ZMod 3329) +
      ∑ k, (v k : ZMod 3329) * A i (k.castLE (by omega)))
    {r : ℝ} (hr : 0 ≤ r) (hs : sqLength o + sqLength v ≤ r^2) :
    ∃ z : CoordSpace 505, ‖z‖ ≤ r ∧
      (retained (history A) j).M.mkQ z =
        (retained (history A) j).M.mkQ (∑ i, b i • (retained (history A) j).g i) := by
  have comp : compatible (history A) o v b := by
    intro i
    rw [hc i]
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [past, dite_eq_left (show k.val < 511 by omega), history]
    rfl
  obtain ⟨w, hw, hn⟩ := retained_realizes (history A) j o v b comp
  refine ⟨w + shift (retained (history A) j) b, ?_, ?_⟩
  · exact (sq_le_sq₀ (norm_nonneg _) hr).mp (hn.trans hs)
  · have hz : (retained (history A) j).M.mkQ w = 0 := (Quotient.mk_eq_zero _).2 hw
    rw [map_add, hz, zero_add]
    rfl

/-- Embed an integer prefix by setting all later input coordinates to zero. -/
def prefixZeroExtend {k n : ℕ} (h : k ≤ n) (v : Fin k → ℤ) : Fin n → ℤ :=
  Function.extend (Fin.castLEEmb h) v (fun _ ↦ 0)

private theorem sum_prefixZeroExtend {k n : ℕ} (h : k ≤ n) (v : Fin k → ℤ)
    {M : Type*} [AddCommMonoid M] (f : Fin n → ℤ → M) (hzero : ∀ i, f i 0 = 0) :
    (∑ i, f i (prefixZeroExtend h v i)) = ∑ i, f (i.castLE h) (v i) := by
  let e := Fin.castLEEmb h
  have hs : (∑ i ∈ univ.map e, f i (prefixZeroExtend h v i)) =
      ∑ i, f i (prefixZeroExtend h v i) := by
    apply sum_subset (subset_univ _)
    intro i _ hi
    have hn : ¬ ∃ a, e a = i := by simpa using hi
    exact (congrArg (f i) (Function.extend_apply' v (fun _ ↦ (0 : ℤ)) i hn)).trans
      (hzero i)
  rw [← hs, sum_map]
  apply sum_congr rfl
  intro i _
  exact congrArg (f (e i)) (e.injective.extend_apply v (fun _ ↦ (0 : ℤ)) i)

/-- Zero extension preserves the raw squared length exactly. -/
theorem sqLength_prefixZeroExtend {k n : ℕ} (h : k ≤ n) (v : Fin k → ℤ) :
    sqLength (prefixZeroExtend h v) = sqLength v := by
  exact sum_prefixZeroExtend h v (fun _ z ↦ (z : ℝ)^2) (by intro i; simp)

/-- A witness from any shorter fixed prefix survives in every later retained state.
The original affine equations and length bound need only refer to the shorter prefix. -/
theorem retained_coset_representative_of_prefix (A : Sample) {j k : ℕ}
    (hj : j ≤ 406) (hk : k ≤ 105+j)
    (o : Fin 400 → ℤ) (v : Fin k → ℤ) (b : Fin 400 → ℤ)
    (hc : ∀ i, (o i : ZMod 3329) = (b i : ZMod 3329) +
      ∑ t, (v t : ZMod 3329) * A i (t.castLE (by omega)))
    {r : ℝ} (hr : 0 ≤ r) (hs : sqLength o + sqLength v ≤ r^2) :
    ∃ z : CoordSpace 505, ‖z‖ ≤ r ∧
      (retained (history A) j).M.mkQ z =
        (retained (history A) j).M.mkQ (∑ i, b i • (retained (history A) j).g i) := by
  refine retained_coset_representative A hj o (prefixZeroExtend hk v) b ?_ hr ?_
  · intro i
    have he := sum_prefixZeroExtend hk v
      (fun t z ↦ (z : ZMod 3329) * A i (t.castLE (by omega))) (by intro t; simp)
    rw [he]
    exact hc i
  · simpa only [sqLength_prefixZeroExtend] using hs

end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.winner_le_of_raw_vector
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.retained_coset_representative
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.sqLength_prefixZeroExtend
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.retained_coset_representative_of_prefix
