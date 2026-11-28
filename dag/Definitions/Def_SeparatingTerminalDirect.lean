import Definitions.Def_SeparatingTerminalMachine

namespace SeparatingTerminalMachine.Direct

open SigabaNeo Turing MultiTapeTM

/-- One input step emits at most one bit and immediately advances the input head. -/
def scan (plan : List Op) : MultiTapeTM 0 Bool (Q plan.length) :=
  ofTr (reader plan).q₀ fun q input _ ↦
    match input with
    | none => { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
    | some x =>
      { inputTape := 1, workTapes := Fin.elim0, output := ((reader plan).step q x).2.head?,
        state := some ((reader plan).step q x).1 }

def config {S : Type} (w : List Bool) (q : Option S) (pos : Fin (w.length + 2)) (o : List Bool) :
    Cfg 0 Bool S w := ⟨q, pos, fun _ _ ↦ none, fun _ ↦ 0, o⟩

theorem read_one (plan w) (q : Q plan.length) (o) {i : ℕ} (h : i < List.length w) :
    (scan plan).step (config w (some q) ⟨i+1,by omega⟩ o) =
    config w (some ((reader plan).step q w[i]).1) ⟨i+2,by omega⟩
      (o ++ ((reader plan).step q w[i]).2) := by
  have hs : (config w (some q) ⟨i+1,by omega⟩ o).inputSymbol = some w[i] :=
    inputSymbolInner i (by simp [config]; omega) h
  rw [step_of_state rfl, hs, scan, tr_ofTr]
  refine Cfg.ext_zero_tapes ?_ ?_ ?_
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [config]; omega)
  · simp only [config, Action.apply, reader, emit]
    split <;> rfl

theorem read_end (plan w) (q : Q plan.length) (o) :
    (scan plan).step (config w (some q) ⟨w.length+1,by omega⟩ o) =
    config w none ⟨w.length+1,by omega⟩ o := by
  have hs : (config w (some q) ⟨w.length+1,by omega⟩ o).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [step_of_state rfl, hs, scan, tr_ofTr]
  apply Cfg.ext_zero_tapes <;> simp [config, Action.apply]

theorem suffix_run (plan w) {i : ℕ} (hi : i ≤ List.length w) (q : Q plan.length) (o) :
    (scan plan).runFrom (config w (some q) ⟨i+1, by omega⟩ o) (w.length-i+1) =
    config w none ⟨w.length+1,by omega⟩ (o ++ (reader plan).run q (w.drop i)) := by
  obtain ⟨n, hn⟩ : ∃ n, w.length-i = n := ⟨_,rfl⟩
  induction n generalizing i q o with
  | zero =>
    obtain rfl : i = w.length := by omega
    simp [read_end, runFrom_one, reader]
  | succ n ih =>
    have hlt : i < w.length := by omega
    change (scan plan).runFrom _ (w.length-i+1) = _
    rw [show w.length-i+1 = 1+(w.length-(i+1)+1) by omega, runFrom_add, runFrom_one,
      read_one _ _ _ _ hlt, ih (i := i+1) (by omega) _ _ (by omega),
      List.drop_eq_getElem_cons hlt, Transducer.run_cons, List.append_assoc]

noncomputable def encoder (plan : List Op) : Machine :=
  Machine.ofTM (scan plan) (plan.length+1)

theorem run_encoder (plan w) (hw : List.length w = List.length plan) :
    (encoder plan).run w = PMF.pure ((reader plan).run (reader plan).q₀ w) := by
  rw [encoder, Machine.run_ofTM]
  have h0 : (scan plan).initCfg w = config w (some (reader plan).q₀) ⟨1,by omega⟩ [] :=
    Cfg.ext_zero_tapes rfl (Fin.ext (by simp [MultiTapeNTM.initCfg, Cfg.init, config])) rfl
  rw [show plan.length+1 = w.length+1 by omega, h0]
  have h := congrArg Cfg.output (suffix_run plan w (i := 0) (Nat.zero_le _) (reader plan).q₀ [])
  simpa [config] using congrArg PMF.pure h

theorem cost_encoder (plan : List Op) :
    (encoder plan).cost = (plan.length+1) +
    6 * ((plan.length+1)*8) * (4 + Nat.size ((plan.length+1)*8)) := by
  have hs : (encoder plan).states = (plan.length+1)*8 := by
    change Nat.card (Q plan.length) = _
    simp [Q, Registers, Nat.card_eq_fintype_card]
  unfold Machine.cost Machine.descLen Machine.entryBits
  rw [hs]
  change _ + 6 * _ * 3^0 * 3^0 * (4 + 4*0 + 4*0 + Nat.size 0 + Nat.size _) = _
  simp [encoder, Machine.ofTM, Nat.size_zero]

noncomputable def dense : Machine := encoder fixedPlan

theorem dense_cost : dense.cost = 1035607808 := by
  rw [dense, cost_encoder, fixedPlan, plan_length]
  have ht : terms.length = 63 := by simp [terms]
  have hs : slots.length = 12672 := by simp [slots]
  rw [ht,hs]; decide

theorem same_run (plan : List Op) (l : List (Op × Bool)) (hp : plan = l.map Prod.fst) :
    (encoder plan).run (l.map Prod.snd) = (machine plan).run (l.map Prod.snd) := by
  have hl : (l.map Prod.snd).length = plan.length := by rw [hp]; simp
  rw [run_encoder _ _ hl, run_machine _ _ hp]
  exact congrArg PMF.pure (run_suffix plan [] l (by simpa only [List.nil_append] using hp) 0 rfl _)

theorem dense_run (b : Bool) (u v : Term → Bool) (pad : Term → Slot → Bool) :
    dense.run ((packet terms slots Prod.fst allow b u v pad).map Prod.snd) =
    encCorrection.run ((packet terms slots Prod.fst allow b u v pad).map Prod.snd) :=
  same_run _ _ (plan_packet ..)

end SeparatingTerminalMachine.Direct
