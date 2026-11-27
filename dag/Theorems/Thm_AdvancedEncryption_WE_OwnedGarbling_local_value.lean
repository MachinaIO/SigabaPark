import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.local_value (x y : Wire) (env : Nat → Bool) (k : Nat)
    (fresh : joint x.ref y.ref = true →
      env k = !(value env x && value env y)) :
    value env (combine k x y) = !(value env x && value env y) := by sorry
