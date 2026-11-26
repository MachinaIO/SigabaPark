import SigabaNeo.Trusted.Assumption
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
Prefix locality of bounded runs. `runFrom_eq_of_prefix_agree` and `run_take_of_le` are copied from
cslib-frontier's `Turing.MultiTapeMachine` (`MultiTape/Probabilistic/PrefixLocality.lean`, Samuel
Schlesinger, Apache 2.0), whose module is not prebuilt in the environment.
-/

namespace AdvancedEncryption.WE.Reach.Local

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

end AdvancedEncryption.WE.Reach.Local

open SigabaNeo

theorem machine_run_take_of_le (A : Machine) {m : ℕ} (hm : A.time ≤ m) (x : List Bool) :
    A.run (x.take m) = A.run x := by
  unfold Machine.run
  congr 1
  exact AdvancedEncryption.WE.Reach.Local.run_take_of_le A.machine _ _ hm x

theorem solution (D D' : PMF (List Bool)) (m k : ℕ)
    (h : D.map (List.take m) = D'.map (List.take m)) (hk : (2 : ℝ) ^ k ≤ m + 1) :
    (Problem.decision D D').HardAt k := by
  intro A
  by_cases ht : A.time ≤ m
  · have hb : ∀ E : PMF (List Bool), E.bind A.run = (E.map (List.take m)).bind A.run := by
      intro E
      rw [PMF.bind_map]
      congr 1
      funext x
      exact (machine_run_take_of_le A ht x).symm
    have he : A.acceptProb D = A.acceptProb D' := by
      unfold Machine.acceptProb
      rw [hb D, hb D', h]
    simp only [Problem.gain, he, sub_self]
    have := A.one_le_cost
    norm_num
  · have hg := (Problem.decision D D').gain_le_one A
    have hc : (m : ℝ) + 1 ≤ A.cost := by
      have : m + 1 ≤ A.cost := by unfold Machine.cost; omega
      exact_mod_cast this
    calc (2 : ℝ) ^ k * (Problem.decision D D').gain A ≤ (2 : ℝ) ^ k * 1 :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ A.cost := by rw [mul_one]; exact hk.trans hc
