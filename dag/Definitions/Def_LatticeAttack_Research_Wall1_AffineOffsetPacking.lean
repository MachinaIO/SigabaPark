import Definitions.Def_LatticeAttack_Research_Wall1_AffineGraphMoments

set_option autoImplicit true

/-! Uniform matrix and independent offset packed into one uniform affine design. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Finset QaryMembership

/-- Column zero is the offset; all subsequent columns are the original matrix. -/
def offsetDesignEquiv (m n q : ℕ) :
    (Design m n q × (Fin m → ZMod q)) ≃ Design m (n+1) q where
  toFun p := fun i ↦ Fin.cons (p.2 i) (p.1 i)
  invFun B := (fun i j ↦ B i j.succ, fun i ↦ B i 0)
  left_inv p := by
    apply Prod.ext <;> funext i
    · funext j
      simp
    · simp
  right_inv B := by
    funext i j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

/-- The product uniform law equals the uniform law of the packed affine design. -/
theorem average_offsetDesign {m n q : ℕ} [Fact q.Prime]
    (f : Design m (n+1) q → ℝ) :
    (∑ A : Design m n q, ∑ c : Fin m → ZMod q, f (offsetDesignEquiv m n q (A,c))) /
      ((Fintype.card (Design m n q) : ℝ) * Fintype.card (Fin m → ZMod q)) = average f := by
  have hs := (offsetDesignEquiv m n q).sum_comp f
  simp only [Fintype.sum_prod_type] at hs
  have hc := Fintype.card_congr (offsetDesignEquiv m n q)
  rw [Fintype.card_prod] at hc
  unfold average
  rw [hs, ← hc, Nat.cast_mul]

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.average_offsetDesign
