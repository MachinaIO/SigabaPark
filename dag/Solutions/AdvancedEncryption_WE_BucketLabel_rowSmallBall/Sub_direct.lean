import Definitions.Def_BucketLabel
open BucketLabel
theorem solution : ∀ d c : Fin 16, d.val ∈ ([1,2,14,15] : List Nat) →
    ((List.range 16).filter (fun a => good a d.val c.val)).length ≤ 6 := by decide
