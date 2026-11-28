import Mathlib

namespace NandWalshBox

def zeroThree (f : Fin 4 → ℚ) : Prop :=
  f 0 - f 1 + f 2 - f 3 = 0 ∧ f 0 + f 1 - f 2 - f 3 = 0 ∧
  f 0 - f 1 - f 2 + f 3 = 0

def admissible (M : Matrix (Fin 4) (Fin 4) ℚ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∑ i, ∑ j, M i j) = 4 ∧
  zeroThree (fun i => ∑ j, M i j) ∧ zeroThree (fun j => ∑ i, M i j)

def raw (u v : Fin 4) : Nat :=
  Nat.xor (![0,1,14,15] u) (![0,3,5,6] v)

def forbidden (n : Nat) : Bool :=
  (n.testBit 1 && n.testBit 2) != (n.testBit 0 && (n.testBit 0 ^^ n.testBit 3))

theorem rowOnes (f : Fin 4 → ℚ) (tot : ∑ i, f i = 4) (z : zeroThree f) :
    ∀ i, f i = 1 := by
  obtain ⟨a,b,c⟩ := z
  simp only [Fin.sum_univ_four] at tot
  intro i
  fin_cases i
  · change f 0 = 1
    linarith
  · change f 1 = 1
    linarith
  · change f 2 = 1
    linarith
  · change f 3 = 1
    linarith


def xor4 (i j : Fin 4) : Fin 4 := ⟨Nat.xor i.val j.val % 4, Nat.mod_lt _ (by decide)⟩


def flip (h k x r : Bool) : Bool := r ^^ (h ^^ (x && k))



def one (x y z : Bool) : Prop := x.toNat + y.toNat + z.toNat = 1

def liftOK (a b c : Bool) (t : Bool × Bool × Bool × Bool × Bool) : Prop :=
  let (u,v,w,z,s) := t
  one u v s ∧ one w z (!s) ∧ a = (w ^^ z) ∧ b = (v ^^ z) ∧ c = (u ^^ v ^^ w)

instance (a b c : Bool) (t : Bool × Bool × Bool × Bool × Bool) : Decidable (liftOK a b c t) := by
  unfold liftOK one
  infer_instance



end NandWalshBox
