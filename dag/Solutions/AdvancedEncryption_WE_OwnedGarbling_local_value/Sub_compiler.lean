import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution (x y : Wire) (env : Nat → Bool) (k : Nat)
    (fresh : joint x.ref y.ref = true →
      env k = !(value env x && value env y)) :
    value env (combine k x y) = !(value env x && value env y) := by
  rcases x with ⟨xr, f⟩
  rcases y with ⟨yr, g⟩
  cases xr with
  | none => cases yr <;> rfl
  | some i =>
    cases yr with
    | none => rfl
    | some j =>
      by_cases h : i = j
      · subst j
        simp [value, combine, shape, joint, atBit]
      · simpa [value, combine, shape, joint, atBit, h] using fresh (by simp [joint, h])
