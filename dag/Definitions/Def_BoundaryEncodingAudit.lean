import SigabaNeoStd.Lattices.RingLWEWord
import SigabaNeoStd.Machines.Gates
import SigabaNeo.Trusted.Primitive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Tactic

/-!
Prefix locality of bounded runs. `runFrom_eq_of_prefix_agree` and `run_take_of_le` are copied from
cslib-frontier's `Turing.MultiTapeMachine` (`MultiTape/Probabilistic/PrefixLocality.lean`, Samuel
Schlesinger, Apache 2.0), whose module is not prebuilt in the environment.
-/

namespace BoundaryEncodingAudit.PrefixLocal

open Cslib Turing Turing.MultiTapeMachine

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : Choose (Action k Symbol State Oracle) → OracleComp spec (Action k Symbol State Oracle))
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

theorem runFrom_eq_of_prefix_agree {input₁ input₂ : List Symbol} {m : ℕ}
    (hm₁ : m ≤ input₁.length) (hm₂ : m ≤ input₂.length)
    (hagree : ∀ j < m, input₁[j]? = input₂[j]?) (fuel : ℕ)
    (cfg₁ : Config k Symbol State Oracle input₁)
    (cfg₂ : Config k Symbol State Oracle input₂)
    (hstate : cfg₁.tapes.state = cfg₂.tapes.state)
    (hpos : cfg₁.tapes.inputPos.val = cfg₂.tapes.inputPos.val)
    (hwork : cfg₁.tapes.workTapes = cfg₂.tapes.workTapes)
    (hworkPos : cfg₁.tapes.workTapePos = cfg₂.tapes.workTapePos)
    (hout : cfg₁.tapes.output = cfg₂.tapes.output)
    (hchan : cfg₁.channels = cfg₂.channels)
    (hbound : cfg₁.tapes.inputPos.val + fuel ≤ m + 1) :
    machine.runFrom choose query fuel cfg₁ = machine.runFrom choose query fuel cfg₂ := by
  induction fuel generalizing cfg₁ cfg₂ with
  | zero => simp [hout]
  | succ fuel ih =>
    cases hs₁ : cfg₁.tapes.state with
    | none =>
      have hs₂ : cfg₂.tapes.state = none := hstate ▸ hs₁
      simp [runFrom, runConfigFrom, hs₁, hs₂, hout]
    | some state =>
      have hs₂ : cfg₂.tapes.state = some state := hstate ▸ hs₁
      have hsym : cfg₁.tapes.inputSymbol = cfg₂.tapes.inputSymbol := by
        rw [Cfg.inputSymbol_eq_inputAt, Cfg.inputSymbol_eq_inputAt, ← hpos, inputAt, inputAt]
        split_ifs
        · rfl
        · exact hagree _ (by lia)
      have hworkSym : cfg₁.tapes.workTapeSymbols = cfg₂.tapes.workTapeSymbols := by
        funext i
        simp [Cfg.workTapeSymbols, hwork, hworkPos]
      have hansSym : cfg₁.answerSymbols = cfg₂.answerSymbols := by
        funext op
        simp [Config.answerSymbols, hchan]
      simp only [runFrom, runConfigFrom, hs₁, hs₂, hsym, hworkSym, hansSym, map_bind]
      congr 1
      funext action
      cases action with
      | step action symbol move =>
        have hmove₁ := val_moveInputPos_eq cfg₁.tapes.inputPos action.inputTape
        have hmove₂ := val_moveInputPos_eq cfg₂.tapes.inputPos action.inputTape
        have hcast : (action.inputTape.cast : ℤ) = -1 ∨ (action.inputTape.cast : ℤ) = 0 ∨
            (action.inputTape.cast : ℤ) = 1 := by
          rcases action.inputTape with _ | _ | _ <;> simp [SignType.cast]
        refine ih (cfg₁.step action symbol move) (cfg₂.step action symbol move)
          rfl ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [Config.step, Turing.Action.apply_inputPos]
          lia
        · funext i
          simp [Config.step, Turing.Action.apply_workTapes, hwork, hworkPos]
        · funext i
          simp [Config.step, Turing.Action.apply_workTapePos, hworkPos]
        · simp [Config.step, Turing.Action.apply_output, hout]
        · funext op
          simp [Config.step, hchan]
        · simp only [Config.step, Turing.Action.apply_inputPos]
          lia
      | query op next =>
        have hq : (cfg₁.channels op).queryBuffer = (cfg₂.channels op).queryBuffer := by
          rw [hchan]
        simp only [hq, map_bind]
        congr 1
        funext answer
        refine ih (cfg₁.receive op next answer) (cfg₂.receive op next answer)
          rfl hpos hwork hworkPos hout ?_ (by simp [Config.receive]; lia)
        funext other
        simp [Config.receive, hchan]

/-- A `fuel`-step run from the initial configuration depends only on the first `m` input symbols
whenever `fuel ≤ m`: starting at `inputPos = 1`, the input head reads only indices below `fuel`. -/
theorem run_take_of_le {fuel m : ℕ} (hm : fuel ≤ m) (input : List Symbol) :
    machine.run choose query fuel (input.take m) = machine.run choose query fuel input := by
  rcases le_or_gt input.length m with hlen | hlen
  · rw [List.take_of_length_le hlen]
  · exact runFrom_eq_of_prefix_agree machine choose query
      (by simp [List.length_take_of_le hlen.le]) hlen.le
      (fun j hj => List.getElem?_take_of_lt hj) fuel
      (machine.initialConfig (input.take m)) (machine.initialConfig input)
      rfl rfl rfl rfl rfl rfl (by simp [initialConfig]; lia)

end BoundaryEncodingAudit.PrefixLocal

open SigabaNeo

theorem BoundaryEncodingAudit.machine_run_take_of_le (A : Machine) {m : ℕ} (hm : A.time ≤ m) (x : List Bool) :
    A.run (x.take m) = A.run x := by
  unfold Machine.run
  congr 1
  exact BoundaryEncodingAudit.PrefixLocal.run_take_of_le A.machine _ _ hm x


namespace BoundaryEncodingAudit
open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape Cslib Turing.MultiTapeTM
def point : RingLWE.Params := ⟨1024,548,16,.cbd 1,.uniform,by decide⟩
noncomputable def assumption : Assumption := RingLWE.decision
theorem point_game : assumption.problem point =
    Problem.decision (ModuleLWE.realLaw point.toModule) (ModuleLWE.idealLaw point.toModule) := rfl

theorem lengths : RingLWEWord.encLen 548 1024 4=20692480001 ∧
    2*548*1024*4=4489216 := by decide

def budget : Nat := 500*(20692480001+4+4489216+9)^3+
  6*3^13*(60*(4+4489216)+5518)*(60*(4+4489216)+5574)
theorem parse_cost : (Prog.decodeM false 4 4489216 20692480001).cost ≤ budget :=
  Prog.cost_decodeM_le _ _ _ _
theorem budget_bits : budget=4432923803936027597344883446924616 ∧ budget<2^112 := by decide

def prefixWord (param : List Bool) (gs : GateList) := frame param ++ frame (encGates gs)

theorem gate_size (gs : GateList) : 3*gs.length≤(encGates gs).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [encList_cons,List.length_append,length_frame,length_encPair,encUnary_apply,
      List.length_replicate,List.length_cons] at ih ⊢
    change 3*gs.length≤((encList encGate) gs).length at ih
    omega

theorem prefix_min (param : List Bool) (gs : GateList) (h : gs.length=4096) :
    24578 ≤ (prefixWord param gs).length := by
  have := gate_size gs
  simp only [prefixWord,List.length_append,length_frame]
  omega

theorem tuple_split (param ct : List Bool) (gs : GateList) :
    encodeTuple [param,encGates gs,ct]=prefixWord param gs++frame ct := by
  simp [encodeTuple,encList_cons,prefixWord,List.append_assoc]

theorem run_take (A : Machine) (w : List Bool) : A.run (w.take A.time)=A.run w := by
  exact machine_run_take_of_le A le_rfl w

theorem blind (A : Machine) (u v : List Bool) (h : A.time≤u.length) : A.run (u++v)=A.run u := by
  rw [← machine_run_take_of_le A h (u++v),← machine_run_take_of_le A h u]
  simp

theorem short_law (A : Machine) (param : List Bool) (gs : GateList) (h : gs.length=4096)
    (d : PMF (List Bool)) (ht : A.time≤24578) :
    (d.map (fun ct ↦ encodeTuple [param,encGates gs,ct])).bind A.run =
    A.run (prefixWord param gs) := by
  rw [PMF.bind_map]
  change (d.bind fun ct ↦ A.run (encodeTuple [param,encGates gs,ct]))=_
  simp only [tuple_split,blind A _ _ (ht.trans (prefix_min param gs h))]
  exact PMF.bind_const _ _

theorem parser_share (A : Machine) (h : 24578<A.time) : budget < 2^98*A.cost := by
  have hN : budget<2^98*24578 := by decide
  unfold Machine.cost; omega

/-- Spending H=233 hardness at squared-gap loss four leaves 103 bits
of multiplicative simulation overhead for an exact 128-bit target. -/
theorem ratio (a sim gap : ℝ) (h : 2^233*(gap/2)^2≤sim) (c : sim≤2^103*a) :
    2^128*gap^2≤a := by nlinarith

theorem exact_machine_bound (D₀ D₁ : PMF (List Bool)) (A B : Machine)
    (hh : RingLWE.decision.HardAt point 233)
    (transfer : (Problem.decision D₀ D₁).gain A ≤ 4*(RingLWE.decision.problem point).gain B)
    (hc : B.cost≤2^103*A.cost) :
    2^128*(Problem.decision D₀ D₁).gain A≤A.cost := by
  have hb := hh B
  have cc : (B.cost:ℝ) ≤ (2:ℝ)^103*A.cost := by exact_mod_cast hc
  change (2:ℝ)^233*(RingLWE.decision.problem point).gain B≤B.cost at hb
  linarith only [transfer,hb,cc]

end BoundaryEncodingAudit
