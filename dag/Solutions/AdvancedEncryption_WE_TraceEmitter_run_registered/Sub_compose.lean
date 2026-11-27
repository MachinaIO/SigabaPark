import Theorems.Thm_AdvancedEncryption_WE_TraceEmitter_load_registered
import Theorems.Thm_AdvancedEncryption_WE_TraceEmitter_gate_replay
import Definitions.Def_WE_CircuitSAT

open Turing SigabaNeo AdvancedEncryption.WE AdvancedEncryption.WE.TraceEmitter

private theorem replay (x s : List Bool) (p : ℕ) (hp : p ≤ x.length)
    (gs : GateList) (k : ℕ) (h out : List Bool) (last : Bool)
    (hk : k ≤ s.length) (hs : s.drop k = encGates gs)
    (valid : ∀ g ∈ gs, g.1 ≤ 4224 ∧ g.2 ≤ 4224)
    (width : h.length + gs.length ≤ 4225) :
    ∃ n ≤ gs.length * 42248 + 1, ∃ trace : List Bool,
      (gs.foldl estep (h,last)).1 = h ++ trace ∧
      tm.runFrom (snap x p s h k 0 (some .first) out) n =
        snap x p s (h++trace) s.length 0 none (out ++ MultiTapeTM.frame trace) := by
  induction gs generalizing k h out last with
  | nil =>
    have he : k = s.length := by
      have := congrArg List.length hs
      change (s.drop k).length = 0 at this
      simp at this
      omega
    subst k
    refine ⟨1, by simp, [], by simp, ?_⟩
    change tm.step _ = _
    have step := tick (q := .first) (q' := none) (move := false) (ds := 0) (dh := 0)
      (sw := none) (hw := none) (emit := some false) (x := x) (p := p)
      (s := s) (h := h) (z := s.length) (j := 0) (out := out) (by simpa)
      (by simp [tr]) (by simp) (by simp)
    simpa [appendOption, MultiTapeTM.frame] using step
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    let u := MultiTapeTM.frame (encGate (a,b))
    let v := !(h.getD a true && h.getD b true)
    have split : s.drop k = u ++ encGates gs := hs
    have hl := congrArg List.length split
    simp only [List.length_drop, List.length_append] at hl
    have head := gate_replay x s h out p k a b (encGates gs) hp hk split
    have hs' : s.drop (k+u.length) = encGates gs := by
      simpa [List.drop_drop] using congrArg (List.drop u.length) split
    obtain ⟨n,lim,t,eq,run⟩ := ih (k+u.length) (h++[v]) (out++[true,v]) v (by omega)
      hs' (by intro g hg; exact valid g (List.mem_cons_of_mem _ hg))
      (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using width)
    obtain ⟨ha,hb⟩ := valid (a,b) (by simp)
    refine ⟨n+(5*a+3*b+2*h.length+8), ?_, v::t, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at width ⊢
      omega
    · change (gs.foldl estep (h++[v],v)).1 = _
      simpa [List.append_assoc] using eq
    · unfold MultiTapeTM.runFrom at *
      rw [Function.iterate_add_apply, head]
      simpa [u,v,MultiTapeTM.frame,List.append_assoc] using run

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 12000 in
theorem solution (φ : CircuitSAT.Circuit 128 4096) (w : Fin 128 → Bool) (ct : List Bool) :
    let rel := CircuitSAT.relation 128 4096
    let word := encodeTuple [paramsWord rel CircuitSAT.params, rel.encStmt φ, rel.encWit w, ct]
    let hist := true :: List.ofFn w
    let trace := (φ.gates.foldl estep (hist,true)).1.drop hist.length
    machine.run word = PMF.pure (MultiTapeTM.frame trace) := by
  let pw := paramsWord (CircuitSAT.relation 128 4096) CircuitSAT.params
  let gs := φ.gates
  let stmt := encGates gs
  let wit := List.ofFn w
  let x := encodeTuple [pw,stmt,wit,ct]
  let h := true :: wit
  let p := 2*pw.length+2*stmt.length+2*wit.length+3
  let setup := 2*pw.length+3*stmt.length+3*wit.length+7
  have pe : pw.length = 515 := by
    change (paramsWord (CircuitSAT.relation 128 4096) CircuitSAT.params).length = 515
    decide
  have we : wit.length = 128 := List.length_ofFn
  have ge : gs.length = 4096 := List.length_ofFn
  have valid : ∀ g ∈ gs, g.1 ≤ 4224 ∧ g.2 ≤ 4224 := by
    intro g hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨Nat.le_of_lt_succ (φ i).1.isLt,Nat.le_of_lt_succ (φ i).2.isLt⟩
  have sl : stmt.length ≤ 103821312 := by
    have e := length_encGates_le (m := 4224) gs valid
    rw [ge] at e
    exact e
  have indexed : x = MultiTapeTM.frame pw ++ MultiTapeTM.frame stmt ++
      MultiTapeTM.frame wit ++ MultiTapeTM.frame ct := by
    change (MultiTapeTM.frame pw ++ (MultiTapeTM.frame stmt ++ (MultiTapeTM.frame wit ++
        (MultiTapeTM.frame ct ++ [])))) = _
    simp [List.append_assoc]
  have loaded : tm.runFrom (tm.initCfg x) setup = snap x p stmt h 0 0 (some .first) := by
    rw [indexed]
    exact load_registered pw stmt wit (MultiTapeTM.frame ct)
  have hp : p ≤ x.length := by rw [indexed]; simp [p,MultiTapeTM.length_frame]; omega
  have he : h.length = 129 := by simp [h,we]
  obtain ⟨n,limit,t,eq,r⟩ := replay x stmt p hp gs 0 h [] true (by omega) (by rfl)
    valid (by omega)
  have both : tm.runFrom (tm.initCfg x) (setup+n) = snap x p stmt (h++t) stmt.length 0 none
      (MultiTapeTM.frame t) := by
    rw [Nat.add_comm, show tm.runFrom (tm.initCfg x) (n+setup) =
        tm.runFrom (tm.runFrom (tm.initCfg x) setup) n from Function.iterate_add_apply .., loaded]
    simpa using r
  have bound : setup+n ≤ clock := by
    rw [ge] at limit
    dsimp [clock,setup]
    omega
  have result := tm.runFrom_eq_of_halt (tm.initCfg x) bound (by rw [both]; rfl)
  change machine.run x = PMF.pure (MultiTapeTM.frame ((gs.foldl estep (h,true)).1.drop h.length))
  rw [machine, Machine.run_ofTM]
  rw [result,both,eq,List.drop_left]
  rfl
