import Mathlib.Data.Bool.Basic

theorem solution (normal orientation override r0 r1 s0 s1 : Bool) :
    let cell := fun p u : Bool =>
      (if p == normal then u ^^ orientation else override) ^^
        (if p then r1 else r0) ^^ (if u then s1 else s0)
    cell true true = !(cell false false ^^ cell false true ^^ cell true false) := by
  cases normal <;> cases orientation <;> cases override <;>
    cases r0 <;> cases r1 <;> cases s0 <;> cases s1 <;> decide
