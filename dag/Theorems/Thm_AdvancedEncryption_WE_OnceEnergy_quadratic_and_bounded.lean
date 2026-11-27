import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceTrace
/-- The nonnegative NAND energy is a quadratic of range at most three per gate plus one. -/
theorem AdvancedEncryption.WE.OnceEnergy.quadratic_and_bounded :
    (∀ x y z : Bool, (pen x y z : ℤ) =
      (x.toNat : ℤ)*y.toNat - 2*(x.toNat : ℤ)*(1-z.toNat) -
      2*(y.toNat : ℤ)*(1-z.toNat)+3*(1-z.toNat)) ∧
    (∀ (s : List Bool × Bool) rows, energy s rows ≤ 3*rows.length+1) := by sorry
