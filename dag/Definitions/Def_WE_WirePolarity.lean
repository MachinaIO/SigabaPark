import Definitions.Def_WE_CircuitSAT

namespace AdvancedEncryption.WE.CircuitSAT.WirePolarity

open SigabaNeo

structure Signs (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)

def run {α : Type} (one : α) (op : α → α → α) (gs : GateList) :
    List α → α → α :=
  gs.foldr (fun g next wires _ ↦
    let v := op (wires.getD g.1 one) (wires.getD g.2 one)
    next (wires ++ [v]) v) (fun _ last ↦ last)

def combine {n : ℕ} (a b : Signs n) : Signs n :=
  ⟨a.neg ∪ b.neg, a.pos ∪ b.pos⟩

def analyze (n : ℕ) (gs : GateList) : Signs n :=
  let one : Signs n := ⟨∅, ∅⟩
  run one combine gs (one :: List.ofFn fun i : Fin n ↦ ⟨{i}, ∅⟩) one

def mixed {n : ℕ} (s : Signs n) := s.pos ∩ s.neg

def liftBits {n : ℕ} (s : Signs n) (z : ↥(mixed s) → Bool) (i : Fin n) : Bool :=
  if h : i ∈ mixed s then z ⟨i,h⟩ else decide (i ∈ s.pos)

def encBit {n : ℕ} (gs : GateList) (β : Bool) : Bool :=
  let s := analyze n gs
  β && decide (∃ z : ↥(mixed s) → Bool, evalGates (List.ofFn (liftBits s z), gs) = true)

end AdvancedEncryption.WE.CircuitSAT.WirePolarity
