import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceTrace
/-- The nonnegative NAND energy is a quadratic of range at most three per gate plus one. -/
theorem solution :
    (∀ x y z : Bool, (pen x y z : ℤ) =
      (x.toNat : ℤ)*y.toNat - 2*(x.toNat : ℤ)*(1-z.toNat) -
      2*(y.toNat : ℤ)*(1-z.toNat)+3*(1-z.toNat)) ∧
    (∀ (s : List Bool × Bool) rows, energy s rows ≤ 3*rows.length+1) := by
  constructor
  · intro x y z
    cases x <;> cases y <;> cases z <;> decide
  · intro s rs
    induction rs generalizing s with
    | nil => cases h : s.2 <;> simp [energy,h]
    | cons p rs ih =>
      obtain ⟨⟨i,j⟩,z⟩ := p
      have hh (x y z : Bool) : pen x y z ≤ 3 := by cases x <;> cases y <;> cases z <;> decide
      have ht := ih (s.1 ++ [z],z)
      have hp := hh (s.1.getD i true) (s.1.getD j true) z
      simp only [energy,List.length_cons]
      omega
