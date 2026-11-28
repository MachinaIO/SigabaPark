import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace OffsetRingCellTree
open Cslib Cslib.Probability SigabaNeo.Lattices
def params : RingLWE.decision.Params :=
  ({N:=2048,m:=1,q:=512,secret:=.cbd 1,error:=.cbd 1} : RingLWE.Params)
abbrev R := Negacyclic (ZMod 512) 2048
abbrev Digit := (Fin 1 → Bool) × (Fin 1 → Bool)
abbrev Seed := Fin 2048 → Digit × Digit
def trit (d : Digit) : ZMod 512 :=
  (((Finset.univ.filter fun i ↦ d.1 i).card : ℤ) -
   ((Finset.univ.filter fun i ↦ d.2 i).card : ℤ) : ZMod 512)
theorem digit_law : (Cslib.Probability.PMF.uniformOfFintype Digit).map trit =
    ModuleLWE.coeffLaw 512 (.cbd 1) := rfl
noncomputable def row (a : R) (s : Seed) : R := a*
  (Negacyclic.ofCoeffs fun i ↦ trit (s i).1) + (Negacyclic.ofCoeffs fun i ↦ trit (s i).2)
def off (b : Bool) := if b then 8193 else 0
def index (b : Bool) (j : Fin 8193) : Fin 18432 := ⟨off b+j.val,by cases b <;> simp [off] <;> omega⟩
def coeffBit (a : R) (j : Fin 18432) : Bool :=
  (a.coeffs ⟨j.val/9,by omega⟩).val.testBit (j.val%9)
def readSeed (bits : Fin 8193 → Bool) : Seed := fun i ↦
  ((fun _ ↦ bits ⟨4*i.val,by omega⟩,fun _ ↦ bits ⟨4*i.val+1,by omega⟩),
   (fun _ ↦ bits ⟨4*i.val+2,by omega⟩,fun _ ↦ bits ⟨4*i.val+3,by omega⟩))
noncomputable def child (a : R) (s : Seed × Bool) (b : Bool) : Seed × Bool :=
  let bits := fun j ↦ coeffBit (row a s.1) (index b j)
  (readSeed bits,s.2 ^^ bits 8192)
noncomputable def cell (a : R) (s : Seed) (u v : Bool) := child a (child a (s,false) u) v
noncomputable def walk (a : R) : Seed × Bool → List Bool → Seed × Bool
  | s,[] => s
  | s,b::xs => walk a (child a s b) xs
theorem shifted (a : R) (seed : Seed) (m : Bool) (xs : List Bool) (r : Bool) :
    walk a (seed,r ^^ m) xs=((walk a (seed,r) xs).1,(walk a (seed,r) xs).2 ^^ m) := by
  induction xs generalizing seed r with
  | nil => rfl
  | cons b xs ih =>
    let bits := fun j ↦ coeffBit (row a seed) (index b j)
    have hx : ((r ^^ m) ^^ bits 8192) = ((r ^^ bits 8192) ^^ m) := by
      cases r <;> cases m <;> cases bits 8192 <;> decide
    change walk a (readSeed bits,(r ^^ m) ^^ bits 8192) xs=_
    rw [hx,ih]; rfl
abbrev Token := Seed × Bool
def addBit (t : Token) (m : Bool) : Token := (t.1,t.2 ^^ m)
def readToken (word : R) (b : Bool) : Token :=
  let raw := fun j ↦ coeffBit word (index b j)
  (readSeed raw,raw 8192)
def optional (flag : Bool) (k : Token) := if flag then some k else none
/-- 10 and 01 receive the disjoint stretches. The common cell 11 uses the private parent. -/
def packets (root : Seed) (word : R) (onlyA onlyB both m : Bool) :=
  ((optional onlyA (readToken word false),optional both (root,false)),
   (optional onlyB (addBit (readToken word true) m),optional both (root,m)))
theorem no_parent (root : Seed) (word : R) (onlyA onlyB m : Bool) :
    packets root word onlyA onlyB false m =
     ((optional onlyA (readToken word false),none),
      (optional onlyB (addBit (readToken word true) m),none)) := rfl

def linearValue (word : R) (x : Fin 12417 → Bool) :=
  (Finset.univ.filter fun i ↦ x i && coeffBit word ⟨i.val,by omega⟩).card % 2 == 1
noncomputable def evaluate (a : R) (k : Token) (x : Fin 12417 → Bool) :=
  linearValue (row a k.1) x ^^ k.2
theorem valueShift (a : R) (k : Token) (m : Bool) (x : Fin 12417 → Bool) :
    evaluate a (addBit k m) x = (evaluate a k x ^^ m) := by
  simp [evaluate,addBit,Bool.xor_assoc]
theorem sizes : 9*2048=18432 ∧ 4*2048=8192 ∧ 2*(8192+1)=16386 ∧
    18432+4*(8192+1)=51204 ∧ 18432+2*(8192+1)=34818 := by decide
end OffsetRingCellTree
