module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_Stages
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import all Definitions.Def_LatticeAttack_Attacks_Bkw_Stages
import all Definitions.Def_LatticeAttack_Attacks_Bkw_Leaves

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

private theorem iidLeaves_weight {E : Type*} (p : PMF E) (a : ℕ) (x : LeafDraw E a) :
    (iidLeaves p a x).toReal = leafWeight (fun z ↦ (p z).toReal) a x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    obtain ⟨l, r⟩ := x
    rw [show iidLeaves p (a + 1) (l, r) = _ from
      independentPair_apply (iidLeaves p a) (iidLeaves p a) l r, ENNReal.toReal_mul, ih, ih]
    rfl

private theorem map_mean {E F : Type*} [Fintype E] [Fintype F] (p : PMF E)
    (f : E → F) (g : F → ℝ) :
    ∑ y, (p.map f y).toReal * g y = ∑ x, (p x).toReal * g (f x) := by
  classical
  simp only [PMF.map_apply, tsum_fintype]
  have h (y : F) := ENNReal.toReal_sum (s := Finset.univ)
    (f := fun x ↦ if y = f x then p x else 0) (by intros; split <;> simp [PMF.apply_ne_top])
  simp_rw [h]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ by
    simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero, ite_mul, zero_mul]
    simp

theorem signedLaw_real_mean {q : ℕ} [NeZero q] (p : PMF (ZMod q)) (a : ℕ) :
    ∑ z, (signedLaw p (a + 1) z).toReal * (ZMod.stdAddChar z).re =
      ‖∑ z, ((p z).toReal : ℂ) * ZMod.stdAddChar z‖ ^ (2 ^ (a + 1)) := by
  have h := errorMean_succ (fun z ↦ (p z).toReal) id ZMod.stdAddChar (by
    intro x y
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ZMod.stdAddChar_apply (-y),
      AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    rfl) a
  rw [errorMean_leaves] at h
  rw [signedLaw, map_mean]
  simpa [-Complex.ofReal_pow, Complex.re_sum, Complex.mul_re, iidLeaves_weight] using congrArg Complex.re h

/-- Count under the convention of one unit per coordinate and one final unit per score term. -/
def scoreOpCount (N q k : ℕ) : ℕ := N * q ^ k * (k + 1)

#print axioms signedLaw_real_mean
#print axioms scoreOpCount

end SigabaNeo.Lattices.Attacks.Bkw
