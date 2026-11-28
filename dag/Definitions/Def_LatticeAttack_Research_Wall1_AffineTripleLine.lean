import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleRank

set_option autoImplicit true

/-! Affine-line structure of rank-two input triples. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Matrix
open scoped Classical
variable {q m n : ℕ} [Fact q.Prime]

/-- Rank two forces the third input onto the affine line through the first two. -/
theorem inputRows_rank_two_affine_line (z : Fin 3 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) (hr : (inputRows z).rank = 2) :
    ∃ t : ZMod q, (z 2).2 = (1-t) • (z 0).2 + t • (z 1).2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hd : (z 1).2 j - (z 0).2 j ≠ 0 := sub_ne_zero.mpr hj.symm
  refine ⟨((z 2).2 j - (z 0).2 j) / ((z 1).2 j - (z 0).2 j), ?_⟩
  funext l
  let c : Fin 3 → Fin (n+1) := ![0, j.succ, l.succ]
  have hdet : ((inputRows z).submatrix id c).det = 0 := by
    by_contra hh
    have hfull := Matrix.rank_of_det_ne_zero hh
    have hle := Matrix.rank_submatrix_le (inputRows z) id c
    rw [hfull, hr] at hle
    norm_num at hle
  simp [Matrix.det_fin_three, Matrix.submatrix, inputRows, augmented, c] at hdet
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hdet

/-- Two different endpoints determine the affine parameter uniquely. -/
theorem affine_line_parameter_unique (x y : Fin n → ZMod q) (hne : x ≠ y)
    {t u : ZMod q} (he : (1-t) • x + t • y = (1-u) • x + u • y) : t = u := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hh := congrFun he j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
  have hz : (t-u)*(y j-x j) = 0 := by linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hj.symm))

/-- An affine input relation also holds for the augmented rows. -/
theorem augmented_affine_line (x y w : Fin n → ZMod q) (t : ZMod q)
    (he : w = (1-t) • x + t • y) :
    augmented w = (1-t) • augmented x + t • augmented y := by
  subst w
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [augmented]
  · simp [augmented]

/-- Consistent outputs obey every affine relation between the corresponding inputs. -/
theorem compatible_outputs_affine_line (z : Fin 3 → Point m n q) (t : ZMod q)
    (he : (z 2).2 = (1-t) • (z 0).2 + t • (z 1).2)
    (hc : ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin) :
    (z 2).1 = (1-t) • (z 0).1 + t • (z 1).1 := by
  have ha := augmented_affine_line _ _ _ t he
  funext i
  obtain ⟨v, hv⟩ := hc i
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  change augmented (z 0).2 ⬝ᵥ v = (z 0).1 i at h0
  change augmented (z 1).2 ⬝ᵥ v = (z 1).1 i at h1
  change augmented (z 2).2 ⬝ᵥ v = (z 2).1 i at h2
  rw [ha, add_dotProduct, smul_dotProduct, smul_dotProduct, h0, h1] at h2
  exact h2.symm

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.inputRows_rank_two_affine_line

#print axioms SigabaNeo.Wall1.AffineGraphMoments.affine_line_parameter_unique
#print axioms SigabaNeo.Wall1.AffineGraphMoments.compatible_outputs_affine_line
