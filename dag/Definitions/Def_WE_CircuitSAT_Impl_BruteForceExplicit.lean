import Definitions.Def_WE_CircuitSAT
import SigabaNeoStd.Machines.Prog.NumBound
import SigabaNeoStd.Machines.Prog.RegMacros
import SigabaNeoStd.Machines.Prog.Arith
import SigabaNeoStd.Machines.Prog.Pass
import SigabaNeoStd.Machines.Prog.Serial
import SigabaNeoStd.Machines.Prog.DetX
import SigabaNeoStd.Machines.Prog.FrameSize
import SigabaNeoStd.Machines.Prog.Sample

/-!
# Brute-force witness encryption with an explicit cost

A submission for `AdvancedEncryption.WE.CircuitSAT.P` that needs no assumption, with an explicit
cost bound `N ≈ 2^187.96`. Both algorithms are tape programs (`SigabaNeo.Tape.Prog`) compiled with
`XProg.toMachineT`.

* `Enc(φ, β)` (`BF.encProg`, 40 tapes) streams its input `encodeTuple [pw, encGates φ, [β]]`
  bit by bit through a three-level frame decoder, evaluating `evalGates` on a wire register of
  `4225` bits (wire `i` at position `4224 - i`, a forward or out-of-range wire reading `true`):
  a lookup, a write and a shift of a one-hot marker are each a single `carry` primitive. It does
  so for every value of a 128-bit counter (8 nested loops of `2^16` rounds), ORs the outputs and
  writes `encodeTuple [[β && sat φ]]`.
* `Dec` (`BF.decProg`) outputs the last three bits of its input, i.e. the frame of the
  ciphertext `[b]`.

The clocks are certified by the numeric interpreter `NB.check` of `SigabaNeoStd`.
-/

namespace SigabaNeo.Tape.BF

open Prog

/-- Lookup: the carry (and every digit) is `∃ pos, A_pos ∧ ¬ G_pos` over the digits so far. -/
def lkOp : DigitOp := fun x y c => (c || (x && !y), c || (x && !y))

/-- Write `b` where the marker is set. -/
def wrOp (b : Bool) : DigitOp := fun x y c => (if y then b else x, c)

end SigabaNeo.Tape.BF

/-!
# The tape programs of brute-force `Enc` and `Dec`
-/

namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

/-- The number of tapes. -/
abbrev K : ℕ := 40

/-- Tape names. -/
abbrev tI : Fin K := 0
abbrev tO : Fin K := 1
abbrev tT16 : Fin K := 2
abbrev tTt : Fin K := 3
abbrev tTf : Fin K := 4
abbrev tH : Fin K := 5
abbrev tQ : Fin K := 6
abbrev tTG : Fin K := 7
abbrev tTA : Fin K := 8
abbrev tTP : Fin K := 9
abbrev tX : Fin K := 10
abbrev tOne : Fin K := 11
abbrev tG : Fin K := 12
abbrev tA : Fin K := 13
abbrev tP : Fin K := 14
abbrev tK : Fin K := 15
abbrev tD : Fin K := 16
abbrev tB : Fin K := 17
abbrev tR : Fin K := 18
abbrev tXC : Fin K := 19
abbrev tMC : Fin K := 20
abbrev fm1 : Fin K := 21
abbrev fv1 : Fin K := 22
abbrev fv2 : Fin K := 23
abbrev fm2 : Fin K := 24
abbrev fm3 : Fin K := 25
abbrev fph : Fin K := 26
abbrev fva : Fin K := 27
abbrev flast : Fin K := 28
abbrev fbeta : Fin K := 29
abbrev fres : Fin K := 30
abbrev tC : Fin K := 31
/-- The counters of the enumeration loops. -/
def cE (i : Fin 8) : Fin K := ⟨32 + i.val, by simp only [K]; omega⟩

def setT (f : Fin K) : Prog K := cp f tTt
def setF (f : Fin K) : Prog K := cp f tTf

/-- `T := T ++ b^|S|` through the counter `tC`. -/
def app (T S : Fin K) (b : Bool) : Prog K := cp tC S ⨾ loop tC (prim (.snoc T b))

/-- `n` doublings of `T` with the bit `b`. -/
noncomputable def dbl (T : Fin K) (b : Bool) : ℕ → Prog K
  | 0 => nop T
  | n + 1 => dbl T b n ⨾ app T T b

/-- The template `1^128` (scratch). -/
noncomputable def sH : Prog K := prim (.snoc tH true) ⨾ dbl tH true 7
/-- The template `1^4096` (scratch). -/
noncomputable def sQ : Prog K := prim (.snoc tQ true) ⨾ dbl tQ true 12
/-- The template of the wire register, `1^4225`. -/
def sTG : Prog K := app tTG tQ true ⨾ app tTG tH true ⨾ prim (.snoc tTG true)
/-- The template of the index marker, `0^4224 1`. -/
def sTA : Prog K := app tTA tQ false ⨾ app tTA tH false ⨾ prim (.snoc tTA true)
/-- The template of the gate marker, `0^4095 1 0^129`. -/
def sTP : Prog K :=
  app tTP tQ false ⨾ tl tTP ⨾ prim (.snoc tTP true) ⨾ app tTP tH false ⨾ prim (.snoc tTP false)
/-- The counter, `0^128`. -/
def sX : Prog K := app tX tH false
/-- The word `0^127 1`. -/
def sOne : Prog K := app tOne tH false ⨾ tl tOne ⨾ prim (.snoc tOne true)
/-- The template of the enumeration counters, `1^65536`. -/
noncomputable def sT16 : Prog K := prim (.snoc tT16 true) ⨾ dbl tT16 true 16

/-- The templates. -/
noncomputable def setup : Prog K :=
  prim (.snoc tTt true) ⨾ prim (.snoc tTf false) ⨾ sH ⨾ sQ ⨾ sTG ⨾ sTA ⨾ sTP ⨾ sX ⨾ sOne ⨾ sT16 ⨾
  prim (.snoc fres false)

/-- `R := lookup`: `hd R = ∃ pos, A_pos ∧ ¬ G_pos`. -/
def look : Prog K := cp tR tA ⨾ prim (.carry lkOp tR tG)

/-- Shift the index marker. -/
def shiftA : Prog K := sin false tA

/-- End of the first index: `va := value`, reset the index, phase B. -/
def pEnd3 : Prog K := look ⨾ ifBit tR (setF fva) (setT fva) ⨾ cp tA tTA ⨾ setT fph

/-- A bit of the gate word `u = frame (1^a) ++ 1^b`. -/
def pStep3 : Prog K :=
  ifBit fph shiftA (ifBit fm3 (setF fm3 ⨾ shiftA) (ifBit tB (setT fm3) pEnd3))

/-- Write the gate value `b`. -/
def wr (b : Bool) : Prog K := prim (.carry (wrOp b) tG tP) ⨾ (if b then setT flast else setF flast)

/-- End of a gate. -/
def pEnd2 : Prog K :=
  look ⨾ ifBit fva (ifBit tR (wr true) (wr false)) (wr true) ⨾
  sin false tP ⨾ cp tA tTA ⨾ setF fph ⨾ setF fm3

/-- A bit of the gate list. -/
def pStep2 : Prog K :=
  ifBit fm2 (setF fm2 ⨾ pStep3) (ifBit tB (setT fm2) pEnd2)

/-- End of a variable of the input tuple. -/
def pEnd1 : Prog K := ifBit fv2 (nop fv2) (ifBit fv1 (setF fv1 ⨾ setT fv2) (setT fv1))

/-- A bit of the input. -/
def pStep1 : Prog K :=
  pp tD tB ⨾
  (ifBit fm1 (setF fm1 ⨾ ifBit fv2 (ifBit tB (setT fbeta) (setF fbeta)) (ifBit fv1 pStep2 (nop fv1)))
    (ifBit tB (setT fm1) pEnd1)) ⨾ clr tB ⨾ clr tR

/-- Initialise the evaluator from the counter `X`. -/
def evalInit : Prog K :=
  cp tG tTG ⨾ cp tXC tX ⨾ moveBits tG tXC tMC ⨾ sin true tG ⨾
  cp tA tTA ⨾ cp tP tTP ⨾
  setF fm1 ⨾ setF fv1 ⨾ setF fv2 ⨾ setF fm2 ⨾ setF fm3 ⨾ setF fph ⨾ setT fva ⨾ setT flast ⨾
  setF fbeta ⨾ cp tK tI ⨾ cp tD tI ⨾ clr tB ⨾ clr tR

/-- Record the result and increment `X`. -/
def evalFin : Prog K := ifBit flast (setT fres) (nop fres) ⨾ prim (.carry addBit tX tOne)

/-- One evaluation of the circuit on the assignment of `X`, then `X := X + 1`. -/
noncomputable def evalOne : Prog K := evalInit ⨾ loop tK pStep1 ⨾ evalFin

/-- The enumeration: `16 m` bits of counting. -/
noncomputable def nest : ℕ → Prog K
  | 0 => evalOne
  | m + 1 => if h : m < 8 then cp (cE ⟨m, h⟩) tT16 ⨾ loop (cE ⟨m, h⟩) (nest m) else nest m

/-- The output frame `[true, β ∧ sat, false]`. -/
def output : Prog K :=
  prim (.snoc tO true) ⨾ ifBit fbeta (ifBit fres (prim (.snoc tO true)) (prim (.snoc tO false)))
    (prim (.snoc tO false)) ⨾ prim (.snoc tO false)

noncomputable def encProg : Prog K := setup ⨾ nest 8 ⨾ output

end SigabaNeo.Tape.BF

namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

/-- `Dec`: tape `0` the input, tape `1` the output (the last three bits of the input), tape `2`
the counter. -/
def decProg : Prog 3 :=
  prim (.snoc 1 false) ⨾ prim (.snoc 1 false) ⨾ prim (.snoc 1 false) ⨾ moveBits 1 0 2

end SigabaNeo.Tape.BF

namespace AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit

open SigabaNeo SigabaNeo.Tape Turing.MultiTapeTM

/-- The relation of the problem. -/
abbrev Rel : Relation := relation inputs size

/-- The longest input of `Enc`. -/
def nE : ℕ := 207643659

/-- The longest input of `Dec` on a ciphertext of `Enc`. -/
def nD : ℕ := 207643916

/-- `Enc`: the brute-force program. -/
noncomputable def encM : Machine := XProg.toMachineT (XProg.prog BF.encProg) BF.tI BF.tO nE

/-- `Dec`: the last three bits of the input. -/
noncomputable def decM : Machine := XProg.toMachineT (XProg.prog BF.decProg) 0 1 nD

theorem coinFree_enc : (XProg.prog BF.encProg).CoinFree := by unfold XProg.CoinFree; decide
theorem coinFree_dec : (XProg.prog BF.decProg).CoinFree := by unfold XProg.CoinFree; decide
theorem wf_enc : (XProg.prog BF.encProg).WF := Prog.wf_of_wfB (by decide)
theorem wf_dec : (XProg.prog BF.decProg).WF := Prog.wf_of_wfB (by decide)

/-- The implementation. -/
noncomputable def impl : Impl WE.sig where
  machine a := if a = Alg.enc then encM else decM
  deterministic a _ := by
    by_cases h : a = Alg.enc
    · simp only [h, ite_true]; exact XProg.deterministic_toMachineT _ coinFree_enc _ _ _
    · simp only [h, ite_false]; exact XProg.deterministic_toMachineT _ coinFree_dec _ _ _

/-- The explicit cost bound, about `2^188`. -/
def N : ℕ := 381461057563519853491131165268104433667487467501207004940

/-- The brute-force submission with an explicit cost. -/
noncomputable def u : Submission P R where
  impl := impl
  deps _ := []
  N := N

end AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit
