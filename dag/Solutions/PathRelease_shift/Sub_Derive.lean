import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem solution {V : Type*} [AddCommGroup V] (T : ℕ → V →+ V) (b : ℕ → V)
    (x d : V) (n : ℕ) : PathRelease.run T b (x+d) n =
      PathRelease.run T b x n + PathRelease.run T (fun _ => 0) d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [PathRelease.run, ih, map_add, add_zero]
    abel
