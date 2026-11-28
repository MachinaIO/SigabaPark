import Mathlib

namespace BinaryBilinearCounts

def sign (b : Bool) : ℤ := if b then -1 else 1

def phase (a b c u v : Bool) := ((a && u) ^^ (b && v)) ^^ (c && (u && v))

def scalarSum (a b c : Bool) : ℤ :=
  sign (phase a b c false false) + sign (phase a b c false true) +
  sign (phase a b c true false) + sign (phase a b c true true)

def step (f : Bool → Bool → ℤ) (a b : Bool) : ℤ :=
  f a b + f (!a) b + f a (!b) - f (!a) (!b)

def discrepancy : Nat → Bool → Bool → ℤ
  | 0 => fun a b => sign (a && b)
  | t+1 => step (discrepancy t)

def origin (a b : Bool) : ℤ := if a || b then 0 else 1

theorem step_sign (c : ℤ) (a b : Bool) :
    step (fun u v => c * sign (u && v)) a b = 4*c*origin a b := by
  cases a <;> cases b <;> simp [step,sign,origin] <;> ring

theorem step_origin (c : ℤ) (a b : Bool) :
    step (fun u v => c * origin u v) a b = c*sign (a && b) := by
  cases a <;> cases b <;> simp [step,sign,origin]

end BinaryBilinearCounts
