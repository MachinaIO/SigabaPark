import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution (st : Nat → Wire) (net : List Gate) :
    (fun i ↦ ((net.foldl emit st) i).ref) =
      net.foldl publicStep (fun i ↦ (st i).ref) := by
  induction net generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    funext i
    by_cases h : i = g.out
    · subst i
      simp [emit, publicStep, combine]
    · simp [emit, publicStep, h]
