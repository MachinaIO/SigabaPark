import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleLine

set_option autoImplicit true

/-! Integer normals encode affine relations and have a minimum nondegenerate norm. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open scoped Classical
variable {q n : ℕ} [Fact q.Prime]

/-- An integer normal with the specified modular ratios encodes exactly the affine relation. -/
theorem affine_relation_iff_integer_normal
    (u v w : ℤ) (t : ZMod q) (hw : (w : ZMod q) ≠ 0)
    (hu : (u : ZMod q) = -(1-t) * (w : ZMod q))
    (hv : (v : ZMod q) = -t * (w : ZMod q))
    (a b c : Fin n → ZMod q) :
    c = (1-t) • a + t • b ↔
      ∀ i, (u : ZMod q)*a i + (v : ZMod q)*b i + (w : ZMod q)*c i = 0 := by
  constructor
  · intro he i
    have hi := congrFun he i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [hu, hv, hi]
    ring
  · intro he
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hi := he i
    rw [hu, hv] at hi
    have hz : (w : ZMod q) * (c i - ((1-t)*a i + t*b i)) = 0 := by
      linear_combination hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hw)

/-- A zero-sum integer normal with no zero coefficient has squared norm at least six. -/
theorem integer_normal_norm_ge_six (u v w : ℤ)
    (hs : u+v+w = 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    6 ≤ u^2 + v^2 + w^2 := by
  have hu1 : 1 ≤ u^2 := by have hp := sq_pos_of_ne_zero hu; omega
  have hv1 : 1 ≤ v^2 := by have hp := sq_pos_of_ne_zero hv; omega
  have hw1 : 1 ≤ w^2 := by have hp := sq_pos_of_ne_zero hw; omega
  by_contra hn
  have hu2 : u^2 ≤ 3 := by omega
  have hv2 : v^2 ≤ 3 := by omega
  have hw2 : w^2 ≤ 3 := by omega
  have hub : -1 ≤ u ∧ u ≤ 1 := by constructor <;> nlinarith
  have hvb : -1 ≤ v ∧ v ≤ 1 := by constructor <;> nlinarith
  have hwb : -1 ≤ w ∧ w ≤ 1 := by constructor <;> nlinarith
  omega

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.affine_relation_iff_integer_normal
#print axioms SigabaNeo.Wall1.AffineGraphMoments.integer_normal_norm_ge_six
