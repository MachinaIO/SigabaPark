module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Mitm

/-- Integer vectors with every coordinate in the closed interval from `-B` to `B`. -/
abbrev IntegerBox (B m : ℕ) := Fin m → ↥(Finset.Icc (-(B : ℤ)) (B : ℤ))

theorem integerBox_card (B m : ℕ) : Fintype.card (IntegerBox B m) = (2 * B + 1) ^ m := by
  simp only [IntegerBox, Fintype.card_fun, Fintype.card_coe, Int.card_Icc, Fintype.card_fin]
  congr 1
  omega

#print axioms integerBox_card

end SigabaNeo.Lattices.Mitm
