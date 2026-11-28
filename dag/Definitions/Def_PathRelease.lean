import Mathlib.Tactic

namespace PathRelease

/-- A layer transfer with an independent or structured additive correction per layer. -/
def run {V : Type*} [AddCommGroup V] (T : ℕ → V →+ V) (b : ℕ → V)
    (x : V) : ℕ → V
  | 0 => x
  | i+1 => T i (run T b x i) + b i

end PathRelease
