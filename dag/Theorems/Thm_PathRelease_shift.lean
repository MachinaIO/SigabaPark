import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem PathRelease.shift {V : Type*} [AddCommGroup V] (T : ℕ → V →+ V) (b : ℕ → V)
    (x d : V) (n : ℕ) : PathRelease.run T b (x+d) n =
      PathRelease.run T b x n + PathRelease.run T (fun _ => 0) d n := by
  sorry
