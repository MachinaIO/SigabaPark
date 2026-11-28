import Mathlib.Tactic
namespace NandEightPhase

def sign (a : Bool) : Int := if a then -1 else 1
def num (x : Bool) : Int := if x then 1 else 0
def form (x y z a b : Bool) : Int :=
  let d := 1-num z
  (1-num x-num y+d)*sign a - (num y-d)*sign a +
      (num x-d)*sign b - d*sign b
def signChar (p : Int) := decide (p%4=3)
def hideChar (p : Int) := decide (p%8=3 ∨ p%8=5)

theorem characters : ∀ x y z a b,
    signChar (form x y z a b) = xor (xor a y) (xor a b && x) ∧
    hideChar (form x y z a b) = (xor a b && xor z (!(x && y))) := by decide

def unit (i : Fin 4) : Int := 2*(i.val : Int)+1
theorem composition : ∀ i j : Fin 4,
    signChar (unit i*unit j) = xor (signChar (unit i)) (signChar (unit j)) ∧
    hideChar (unit i*unit j) = xor (hideChar (unit i)) (hideChar (unit j)) := by decide

end NandEightPhase

namespace NandEightPhase
/-- A single local substitution; XOR-summing with the reverse weights
    telescopes all internal wire discrepancies. -/
theorem discrepancy : ∀ x y z x' y' : Bool,
    xor z (!(x' && y')) =
      xor (xor z (!(x && y))) (xor (y' && xor x x') (x && xor y y')) := by decide
end NandEightPhase

namespace NandEightPhase
abbrev R := ZMod 8
def encode (s h : Bool) : R := if s then (if h then 3 else 7) else (if h then 5 else 1)
def sBit (p : R) : Bool := decide (p=3 ∨ p=7)
def hBit (p : R) : Bool := decide (p=3 ∨ p=5)
def phase (x y z a b : Bool) : R := (form x y z a b : R)
theorem phase_as_code : ∀ x y z a b, phase x y z a b =
    encode (xor (xor a y) (xor a b && x)) (xor a b && xor z (!(x && y))) := by decide
theorem encode_mul : ∀ s h t k, encode s h * encode t k = encode (xor s t) (xor h k) := by decide
theorem decode_code : ∀ s h, sBit (encode s h)=s ∧ hBit (encode s h)=h := by decide

def prefixPhase : List (Bool × Bool) → R
  | [] => 1
  | (a,b)::rs => phase true true false a b * prefixPhase rs

theorem prefix_form (rs : List (Bool × Bool)) : ∃ s, prefixPhase rs = encode s false := by
  induction rs with
  | nil => exact ⟨false,rfl⟩
  | cons ab rs ih =>
    obtain ⟨s,hs⟩ := ih
    obtain ⟨a,b⟩ := ab
    cases a <;> cases b <;> cases s <;> simp only [prefixPhase,hs] <;> first | exact ⟨false,by decide⟩ | exact ⟨true,by decide⟩

def raw (p : R) (a b u v m z : Bool) :=
  p * phase true true z a b * phase z z false u v * encode false m

theorem recover_pair : ∀ s a b u v m,
    xor (hBit (raw (encode s false) a b u v m false))
      (!(xor (sBit (raw (encode s false) a b u v m false))
        (sBit (raw (encode s false) a b u v m true)))) = m := by decide

theorem raw_recovers (rs : List (Bool × Bool)) (a b u v m : Bool) :
    xor (hBit (raw (prefixPhase rs) a b u v m false))
      (!(xor (sBit (raw (prefixPhase rs) a b u v m false))
        (sBit (raw (prefixPhase rs) a b u v m true)))) = m := by
  obtain ⟨s,hs⟩ := prefix_form rs; rw [hs]; apply recover_pair

/-- The prefix value may come from any claimed prefix. Negating one sign of the last
gate and one of the terminal test changes the message while preserving the quotient
at every trace simultaneously. This permutation of fair coins is its own inverse. -/
theorem quotient_shift : ∀ s k a b u v m z, hBit (raw (encode s k) a b u v m z) =
    hBit (raw (encode s k) a (!b) u (!v) (!m) z) := by decide

theorem raw_prefix_any (rs : List (Bool × Bool × Bool)) :
    ∃ s k, rs.foldr (fun r p ↦ phase true true r.1 r.2.1 r.2.2 * p) 1 = encode s k := by
  induction rs with
  | nil => exact ⟨false,false,rfl⟩
  | cons r rs ih =>
    obtain ⟨s,k,h⟩ := ih
    rw [List.foldr_cons,h,phase_as_code,encode_mul]
    exact ⟨_,_,rfl⟩

end NandEightPhase
