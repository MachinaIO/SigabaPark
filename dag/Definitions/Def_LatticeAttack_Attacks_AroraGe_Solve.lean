module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_CenteredRank
import all Definitions.Def_LatticeAttack_Attacks_AroraGe_CenteredRank

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Translation
public import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

variable {q : ℕ} [Fact q.Prime]

/-- The uniform probability bound for the centered rows, with a nonempty error alphabet. -/
theorem centeredRankFailure_probability (E : Finset (ZMod q)) (hE : E.Nonempty)
    (hq : E.card < q) (m : ℕ) :
    ((centeredRankFailures E m).card : ℚ) / ((E.card : ℚ) * q) ^ m ≤
      ((q : ℚ) ^ E.card - 1) * (1 - 1 / ((E.card : ℚ) * q)) ^ m := by
  have hp : 0 < q := (Fact.out : Nat.Prime q).pos
  have hd : 0 < E.card := hE.card_pos
  have h₁ : 1 ≤ q ^ E.card := Nat.one_le_pow _ _ hp
  have h₂ : 1 ≤ E.card * q := Nat.mul_pos hd hp
  have h := centeredRankFailures_card E hq m
  have hc : ((centeredRankFailures E m).card : ℚ) ≤
      ((q : ℚ) ^ E.card - 1) * ((E.card : ℚ) * q - 1) ^ m := by
    have hc' : ((centeredRankFailures E m).card : ℚ) ≤
        (((q ^ E.card - 1 : ℕ) : ℚ) * ((E.card * q - 1 : ℕ) : ℚ) ^ m) := by exact_mod_cast h
    simpa [Nat.cast_sub h₁, Nat.cast_sub h₂] using hc'
  have hn : (E.card : ℚ) * q ≠ 0 := by positivity
  rw [show 1 - 1 / ((E.card : ℚ) * q) = ((E.card : ℚ) * q - 1) / (E.card * q) by
    field_simp, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hc (by positivity)

open Polynomial

/-- Positive-degree coefficient rows up to the common degree bound. -/
def positiveRows {m : ℕ} (D : ℕ) (p : Fin m → (ZMod q)[X]) :
    Matrix (Fin m) (Fin D) (ZMod q) := fun j i ↦ (p j).coeff (i.val + 1)

private theorem leftKernel_iff {m D : ℕ} (p : Fin m → (ZMod q)[X])
    (hd : ∀ j, (p j).natDegree ≤ D) (w : Fin m → ZMod q) :
    w ∈ (positiveRows D p).transpose.mulVecLin.ker ↔
      ∀ k : ℕ, (∑ j, w j • p j).coeff (k + 1) = 0 := by
  classical
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Matrix.mulVec,
    Matrix.transpose_apply, positiveRows, dotProduct, Pi.zero_apply, finsetSum_coeff,
    coeff_smul, smul_eq_mul, mul_comm (w _)]
  constructor
  · intro h k
    by_cases hk : k < D
    · exact h ⟨k, hk⟩
    · exact Finset.sum_eq_zero fun j _ ↦ by
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd j) (by omega)), zero_mul]
  · intro h i
    exact h i.val

theorem translatedPositiveRows_rank {m D : ℕ} (p : Fin m → (ZMod q)[X])
    (hd : ∀ j, (p j).natDegree ≤ D) (s : ZMod q) :
    (positiveRows D (fun j ↦ taylor s (p j))).rank = (positiveRows D p).rank := by
  let A := positiveRows D (fun j ↦ taylor s (p j))
  let B := positiveRows D p
  have hk : A.transpose.mulVecLin.ker = B.transpose.mulVecLin.ker := by
    ext w
    exact (leftKernel_iff _ (fun j ↦ by simpa using hd j) w).trans
      ((translated_positive_relation_iff s Finset.univ p w).trans (leftKernel_iff p hd w).symm)
  change A.rank = B.rank
  rw [← A.rank_transpose, ← B.rank_transpose]
  exact Nat.add_right_cancel (show A.transpose.rank + Module.finrank _ B.transpose.mulVecLin.ker =
      B.transpose.rank + Module.finrank _ B.transpose.mulVecLin.ker by
    calc
      _ = Module.finrank (ZMod q) (Fin m → ZMod q) := by
        rw [← hk]; exact A.transpose.mulVecLin.finrank_range_add_finrank_ker
      _ = _ := B.transpose.mulVecLin.finrank_range_add_finrank_ker.symm)

/-- With row scalar u = -a, shifting the argument by -s gives P(e + a*s - a*X). -/
noncomputable def samplePolynomial (E : Finset (ZMod q)) (r : ZMod q × ZMod q) :
    (ZMod q)[X] := (taylor r.1 (∏ e ∈ E, (X - C e))).comp (C r.2 * X)

noncomputable def translatedFailures (E : Finset (ZMod q)) (m : ℕ) (s : ZMod q) :=
  (Fintype.piFinset fun _ : Fin m ↦ E ×ˢ Finset.univ).filter fun rows ↦
    (positiveRows E.card (fun j ↦ taylor (-s) (samplePolynomial E (rows j)))).rank < E.card

theorem translatedFailure_probability (E : Finset (ZMod q)) (hE : E.Nonempty)
    (hq : E.card < q) (m : ℕ) (s : ZMod q) :
    ((translatedFailures E m s).card : ℚ) / ((E.card : ℚ) * q) ^ m ≤
      ((q : ℚ) ^ E.card - 1) * (1 - 1 / ((E.card : ℚ) * q)) ^ m := by
  classical
  apply le_trans _ (centeredRankFailure_probability E hE hq m)
  gcongr
  intro rows h
  obtain ⟨hm, hr⟩ := Finset.mem_filter.mp h
  have hd (j : Fin m) : (samplePolynomial E (rows j)).natDegree ≤ E.card := by
    unfold samplePolynomial
    apply natDegree_comp_le.trans
    rw [natDegree_taylor]
    have h₂ := natDegree_mul_le (p := C (rows j).2) (q := X)
    simp at h₂
    simpa using Nat.mul_le_mul_left E.card h₂
  rw [translatedPositiveRows_rank _ hd] at hr
  have heq : positiveRows E.card (fun j ↦ samplePolynomial E (rows j)) = centeredMatrix E rows := by
    ext j i
    simp [positiveRows, samplePolynomial, centeredMatrix]
  rw [heq] at hr
  apply (mem_centeredRankFailures_iff E rows (fun j ↦
    (Finset.mem_product.mp (Fintype.mem_piFinset.mp hm j)).1)).mpr
  by_contra! hh
  let A := centeredMatrix E rows
  have hk : A.mulVecLin.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hn
    exact hh v hn hv
  have hn := A.mulVecLin.finrank_range_add_finrank_ker
  rw [hk] at hn
  simp at hn
  change A.rank = E.card at hn
  exact (ne_of_lt hr) hn

#print axioms translatedFailure_probability
#print axioms translatedPositiveRows_rank
#print axioms centeredRankFailure_probability

end SigabaNeo.Lattices.AroraGe
