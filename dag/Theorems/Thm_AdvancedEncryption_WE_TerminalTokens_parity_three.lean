import Mathlib.Data.Bool.Basic

theorem AdvancedEncryption.WE.TerminalTokens.parity_three (normal orientation override r0 r1 s0 s1 : Bool) :
    let cell := fun p u : Bool =>
      (if p == normal then u ^^ orientation else override) ^^
        (if p then r1 else r0) ^^ (if u then s1 else s0)
    cell true true = !(cell false false ^^ cell false true ^^ cell true false) := by
  sorry
