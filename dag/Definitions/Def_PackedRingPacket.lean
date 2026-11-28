import SigabaNeoStd.Lattices.RingLWE
import SigabaNeoStd.Machines.Prog.FrameIO
import Mathlib.Tactic
open scoped BigOperators
open Cslib Cslib.Probability
namespace RingPacket
def assumptions (n w m : ℕ) : SigabaNeo.Lattices.RingLWE.Params where
  N := n
  m := m
  q := 2^(w-1)
  q_pos := Nat.pow_pos (by decide)
  secret := .uniform
  error := .gauss 9
def bankBits (n w copies : ℕ) := copies*2*w*2*n*w
def splitDigit (p : ℕ) : Fin (2*p) ≃ Fin 2 × Fin p where
  toFun x := (⟨x.val%2, Nat.mod_lt _ (by decide)⟩, ⟨x.val/2,by omega⟩)
  invFun x := ⟨x.1.val+2*x.2.val, by have:=x.1.isLt; have:=x.2.isLt;omega⟩
  left_inv x := by apply Fin.ext; dsimp; omega
  right_inv x := by apply Prod.ext <;> apply Fin.ext <;> dsimp <;> have:=x.1.isLt <;> omega

end RingPacket