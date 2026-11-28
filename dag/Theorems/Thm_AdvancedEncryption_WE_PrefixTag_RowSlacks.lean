import Mathlib

theorem AdvancedEncryption.WE.PrefixTag.RowSlacks (x y : Bool) :
    let a : Int := if x then 1 else 0
    let b : Int := if y then 1 else 0
    let z : Int := if !(x && y) then 1 else 0
    (2-a-b-z = 0 ∨ 2-a-b-z = 1) ∧ (z+a-1 = 0 ∨ z+a-1 = 1) := by sorry
