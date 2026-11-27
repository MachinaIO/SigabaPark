import Definitions.Def_WE_CircuitSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

open SigabaNeo AdvancedEncryption AdvancedEncryption.WE AdvancedEncryption.WE.CircuitSAT

/-!
Prefix locality of bounded runs. `runFrom_eq_of_prefix_agree` and `run_take_of_le` are copied from
cslib-frontier's `Turing.MultiTapeMachine` (`MultiTape/Probabilistic/PrefixLocality.lean`, Samuel
Schlesinger, Apache 2.0), whose module is not prebuilt in the environment.
-/

namespace AdvancedEncryption.WE.ClockFloor.Local

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

end AdvancedEncryption.WE.ClockFloor.Local

open SigabaNeo

theorem machine_run_take_of_le (A : Machine) {m : ℕ} (hm : A.time ≤ m) (x : List Bool) :
    A.run (x.take m) = A.run x := by
  unfold Machine.run
  congr 1
  exact AdvancedEncryption.WE.ClockFloor.Local.run_take_of_le A.machine _ _ hm x

open Turing.MultiTapeTM
open scoped ENNReal

private theorem run_common (A : Machine) (p a b : List Bool) (ht : A.time ≤ p.length) :
    A.run (p ++ a) = A.run (p ++ b) := by
  rw [← machine_run_take_of_le A ht (p ++ a), ← machine_run_take_of_le A ht (p ++ b)]
  simp

private theorem gateLen (gs : GateList) :
    (encGates gs).length = (gs.map fun g => 4 * g.1 + 2 * g.2 + 3).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [encList_cons, List.length_append, length_frame, length_encPair, encUnary_apply,
      List.length_replicate, List.map_cons, List.sum_cons] at *
    change ((encList encGate) gs).length = _ at ih
    omega

private theorem forward_fold (j m : ℕ) (w : List Bool) (b : Bool)
    (h : w.length + j ≤ m + 1) :
    ((List.replicate j (m,m)).foldl estep (w,b)).1 = w ++ List.replicate j false := by
  induction j generalizing w b with
  | zero => simp
  | succ j ih =>
    have hg : w.getD m true = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    simp only [List.replicate_succ, List.foldl_cons, estep, hg, Bool.true_and, Bool.not_true]
    rw [ih _ _ (by simp; omega), List.append_assoc]
    rfl

private theorem long_control (n j : ℕ) :
    ∃ (φ : Circuit n (j+2)) (x : Fin n → Bool), Satisfies φ x ∧
      (encCircuit n (j+2) φ).length =
        (j+1)*(6*(n+j+2)+3) + (4*(n+j+2)+2*(n+j+1)+3) := by
  let m := n+j+2
  let φ : Circuit n (j+2) := fun i =>
    (⟨m, by dsimp [m]; omega⟩, if i.val = j+1 then ⟨m-1, by dsimp [m]; omega⟩
      else ⟨m, by dsimp [m]; omega⟩)
  have hgs : φ.gates = List.replicate (j+1) (m,m) ++ [(m,m-1)] := by
    apply List.ext_getElem
    · simp only [Circuit.gates, List.length_ofFn, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
    · intro i hi hj
      by_cases h : i < j+1
      · rw [List.getElem_append_left (by simpa only [List.length_replicate] using h)]
        simp only [Circuit.gates, List.getElem_ofFn, φ, if_neg h.ne, List.getElem_replicate]
      · have he : i = j+1 := by simp only [List.length_append, List.length_replicate,
                                   List.length_cons, List.length_nil] at hj; omega
        subst i
        rw [List.getElem_append_right (by simp)]
        simp only [Circuit.gates, List.getElem_ofFn, φ, ite_true, List.length_replicate,
          Nat.sub_self, List.getElem_cons_zero]
  let x : Fin n → Bool := fun _ => false
  let w := true :: List.ofFn x
  have hw : w.length = n+1 := by simp [w]
  refine ⟨φ, x, ?_, ?_⟩
  · change evalGates (List.ofFn x, φ.gates) = true
    rw [hgs]
    simp only [evalGates, List.foldl_append, List.foldl_cons, List.foldl_nil, estep]
    rw [forward_fold (j+1) m w true (by dsimp [m]; omega)]
    have hl : m-1 < (w ++ List.replicate (j+1) false).length := by simp [m,hw]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
      List.getElem_append_right (show w.length ≤ m-1 by dsimp [m]; omega)]
  · change (encGates φ.gates).length = _
    rw [hgs, gateLen]
    simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, List.sum_append,
      List.sum_replicate, List.sum_cons, List.sum_nil, Nat.add_zero, nsmul_eq_mul]
    dsimp [m]
    ring_nf

private theorem tuple_length (a : List Bool) (l : List (List Bool)) :
    (encodeTuple (a::l)).length = 2*a.length+1+(encodeTuple l).length := by
  simp only [encodeTuple, encList_cons, List.length_append, length_frame, encBits_apply]

private theorem enc_input (pw st : List Bool) (b : Bool) :
    encodeTuple [pw, st, encBit b] = (encodeTuple [pw,st] ++ [true]) ++ [b,false] := by
  simp only [encodeTuple, encList_cons, encList_nil, encBits_apply, List.append_nil,
    List.append_assoc, encBit, frame, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append]

private theorem dec_input (pw st wit ct : List Bool) :
    encodeTuple [pw,st,wit,ct] = (encodeTuple [pw,st] ++ encodeTuple [wit]) ++ frame ct := by
  simp only [encodeTuple, encList_cons, encList_nil, encBits_apply, List.append_nil,
    List.append_assoc]

private theorem distinguish_laws (D : PMF (List Bool)) :
    ¬ (1 - ((2 : ℝ)^128)⁻¹ ≤ (D [false]).toReal ∧
       1 - ((2 : ℝ)^128)⁻¹ ≤ (D [true]).toReal) := by
  intro ⟨hf,ht⟩
  have hs := sum_le_tsum ({[false], [true]} : Finset (List Bool)) (f := fun x => D x)
  simp [D.tsum_coe] at hs
  have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hs
  rw [ENNReal.toReal_add (D.apply_ne_top _) (D.apply_ne_top _), ENNReal.toReal_one] at h
  norm_num at hf ht
  linarith

theorem solution (impl : Impl WE.sig)
    (hc : WE.Correct (relation inputs size) params impl) :
    207643654 ≤ (impl.machine Alg.enc).time ∧ 207643910 ≤ (impl.machine Alg.dec).time := by
  obtain ⟨φ,x,hx,hlen⟩ := long_control 128 4094
  change (encCircuit inputs size φ).length = 103821310 at hlen
  let R : WE.Relation := relation inputs size
  let p := encodeTuple [paramsWord R params, R.encStmt φ]
  let v := encodeTuple [R.encWit x]
  have hp : p.length = 207643652 := by
    change (encodeTuple [paramsWord R params, encCircuit inputs size φ]).length = _
    have hparam : (paramsWord R params).length = 515 := by
      unfold paramsWord
      simp only [tuple_length, List.length_replicate]
      rfl
    rw [tuple_length, tuple_length, hparam, hlen]
    rfl
  have hv : v.length = 257 := by
    have g (n : ℕ) (z : Fin n → Bool) : (encodeTuple [encAssignment n z]).length = 2*n+1 := by
      rw [tuple_length]
      change 2*(List.ofFn z).length+1+0 = _
      simp
    exact g 128 x
  have diff : decryptLaw R params impl φ x false ≠ decryptLaw R params impl φ x true := by
    intro e
    have hf := hc φ x hx false
    have ht := hc φ x hx true
    change 1 - ((2 : ℝ)^128)⁻¹ ≤ (decryptLaw R params impl φ x false [false]).toReal at hf
    rw [e] at hf
    exact distinguish_laws _ ⟨hf,ht⟩
  constructor
  · by_contra! ht
    apply diff
    have he : enc (R := R) params impl φ false = enc (R := R) params impl φ true := by
      have hr := run_common (impl.machine Alg.enc) (p ++ [true]) [false,false] [true,false]
        (by simp only [List.length_append, hp, List.length_cons, List.length_nil]; omega)
      unfold enc Impl.run
      simp only [enc_input]
      rw [hr]
    simp only [decryptLaw, he]
  · by_contra! ht
    apply diff
    have hdec (ct : List Bool) : dec (R := R) params impl φ x ct = dec (R := R) params impl φ x [] := by
      have hr := run_common (impl.machine Alg.dec) (p ++ v) (frame ct) (frame [])
        (by rw [List.length_append,hp,hv]; omega)
      unfold dec Impl.run
      simp only [dec_input]
      rw [hr]
    have e : dec (R := R) params impl φ x = fun _ => dec (R := R) params impl φ x [] :=
      funext hdec
    unfold decryptLaw
    rw [e, PMF.bind_const, PMF.bind_const]
