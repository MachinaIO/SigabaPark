import Mathlib.Tactic
namespace FixedTarget225
def majSeries (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :=
  x * ∑ j ∈ Finset.range n, a j * (1-x^2)^j
def gateDist (a b z : Bool) : Nat := (!z).toNat + (!(z ^^ a)).toNat +
  (!(z ^^ b)).toNat + (z ^^ a ^^ b).toNat
def pm (p : ℝ) (b : Bool) := if b then p else 1-p
def pairGap (p : ℝ) (y : Bool) : ℝ :=
  pm p false * pm p y - pm p true * pm p (!y)
end FixedTarget225
open FixedTarget225
