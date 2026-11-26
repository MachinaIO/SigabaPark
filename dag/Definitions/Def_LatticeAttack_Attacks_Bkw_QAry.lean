import Mathlib.Data.ZMod.Basic
import Definitions.Def_LatticeAttack_Attacks_Bkw_Fourier

set_option autoImplicit true

namespace SigabaNeo.Lattices.Attacks.Bkw

open ComplexConjugate

/-- A matched block pair is specified by its common block and both last coordinates.
Every difference, including zero, has the same number of preimages. -/
theorem matched_difference_card {B : Type*} [Fintype B] {q : ℕ} [NeZero q] (d : ZMod q) :
    Fintype.card {r : B × ZMod q × ZMod q // r.2.1 - r.2.2 = d} = Fintype.card B * q := by
  classical
  let equiv : {r : B × ZMod q × ZMod q // r.2.1 - r.2.2 = d} ≃ B × ZMod q :=
    { toFun := fun r ↦ (r.val.1, r.val.2.2)
      invFun := fun r ↦ ⟨(r.1, d + r.2, r.2), by simp⟩
      left_inv := by
        rintro ⟨⟨b, x, y⟩, h⟩
        change x - y = d at h
        subst d
        simp
      right_inv := fun _ ↦ rfl }
  simpa using Fintype.card_congr equiv

/-- Even with a binary last coordinate and a single possible block, zero occurs twice. -/
theorem binary_zero_difference_card :
    Fintype.card {r : Unit × ZMod 2 × ZMod 2 // r.2.1 - r.2.2 = 0} = 2 := by
  simpa using (matched_difference_card (B := Unit) (0 : ZMod 2))

theorem qary_difference_mean_norm {ι : Type*} [Fintype ι] {q : ℕ}
    (p : ι → ℝ) (e : ι → ZMod q) (ψ : ZMod q → ℂ)
    (hψ : ∀ x y, ψ (x - y) = ψ x * conj (ψ y)) :
    ‖errorMean p e 1 ψ‖ = ‖∑ i, (p i : ℂ) * ψ (e i)‖ ^ 2 := by
  simpa using errorMean_norm p e ψ hψ 1

#print axioms matched_difference_card
#print axioms binary_zero_difference_card
#print axioms qary_difference_mean_norm

end SigabaNeo.Lattices.Attacks.Bkw
