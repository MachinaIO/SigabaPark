import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem solution : ∀ b : Fin 8, b≠0 →
    (Finset.univ.filter (fun a : Fin 8 => dot3 a b)).card=4 := by decide
