import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic
namespace TwoTraceEnergy

def bit (b : Bool) : ℤ := if b then 1 else 0

def h (a b t u s : ℤ) : ℤ :=
  (a - 2*t - 4*b + 2)*u + (-2*a - 4*t + 4)*s + 2*b + 3*t

def localCost (a b t u s : Bool) : ℤ :=
  h (bit a) (bit b) (bit t) (bit u) (bit s)

def total {V : Type*} {n : ℕ} (a b t : V → Fin n → Bool) (v w : V) : ℤ :=
  ∑ j, localCost (a v j) (b v j) (t v j) (b w j) (t w j)

def push (b : Bool) (r : ℕ) : ℤ := if b then 1 + (r : ℤ) else -(r : ℤ)

def pen (x : ℤ) : ℤ := x*(x-1)

end TwoTraceEnergy
namespace TwoTraceEnergy

def zeroRun : SigabaNeo.GateList → List Bool → List Bool → Bool → Bool → Prop
  | [], _, _, p, q => p = true ∧ q = true
  | (i,j)::gs, l, r, _, _ => ∃ z w : Bool,
      localCost (l.getD i true) (l.getD j true) (!z) (r.getD j true) (!w) = 0 ∧
      zeroRun gs (l++[z]) (r++[w]) z w

end TwoTraceEnergy
