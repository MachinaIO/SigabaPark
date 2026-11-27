import SigabaNeoStd.Machines.Gates

namespace AdvancedEncryption.WE.TraceLock

inductive Atom where
  | one | witness (i : ℕ) | gate (i : ℕ)
deriving DecidableEq

inductive Expr where
  | lit (a : Atom) | conj (p q : Expr) | xorGate (p q : Expr)

def Atom.read (w t : ℕ → Bool) : Atom → Bool
  | .one => true | .witness i => w i | .gate i => t i

def Expr.eval (w t : ℕ → Bool) : Expr → Bool
  | .lit a => a.read w t
  | .conj p q => p.eval w t && q.eval w t
  | .xorGate p q => xor (p.eval w t) (q.eval w t)

def Expr.depth : Expr → ℕ
  | .lit _ => 0 | .conj p q | .xorGate p q => max p.depth q.depth + 1

def Expr.gates : Expr → ℕ
  | .lit _ => 0 | .conj p q | .xorGate p q => p.gates + q.gates + 1

/-- Construct literal lookups entirely at circuit compilation time. -/
def flags (h : List Atom) (i : ℕ) : SigabaNeo.GateList → List Expr
  | [] => []
  | (a,b) :: gs =>
    let v := Atom.gate i
    Expr.xorGate (.lit v) (.conj (.lit (h.getD a .one)) (.lit (h.getD b .one))) ::
      flags (h++[v]) (i+1) gs

/-- A complete binary AND tree over consecutive leaves. -/
def tree (g : ℕ → Expr) (i : ℕ) : ℕ → Expr
  | 0 => g i
  | d+1 => .conj (tree g i d) (tree g (i+2^d) d)

def inputs (n : ℕ) := Atom.one :: (List.range n).map Atom.witness

/-- An exact 4096-local-check AND/XOR formula with a separate final wire test. -/
def predicate (gs : SigabaNeo.GateList) : Expr :=
  let fs := flags (inputs 128) 0 gs
  .conj (tree (fun i ↦ fs.getD i (.lit .one)) 0 12) (.lit (.gate 4095))

def segment (f : ℕ → Bool) (i : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => f i :: segment f (i+1) n

end AdvancedEncryption.WE.TraceLock
