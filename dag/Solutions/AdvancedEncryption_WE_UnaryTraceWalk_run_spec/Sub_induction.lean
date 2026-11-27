import Theorems.Thm_AdvancedEncryption_WE_UnaryTraceWalk_lookup_block
import Theorems.Thm_AdvancedEncryption_WE_UnaryTraceWalk_commit_block

open Turing SigabaNeo AdvancedEncryption.WE AdvancedEncryption.WE.UnaryTraceWalk

private def loadState (j : ℕ) : State :=
  if hj : j < 4224 then .inl ⟨j, hj⟩ else .inr .turn

private def loadCfg (u suffix : List Bool) (j : ℕ) : Cfg 2 Bool State (u ++ suffix) :=
  { scanCfg (u ++ suffix) (true :: u.take j) (true :: u.take (min j 128)) j
      ((j : ℤ) + 1) .turn with state := some (loadState j) }

private theorem addTick {x : List Bool} (c : Cfg 2 Bool State x) (j : ℕ) :
    tm.runFrom c (j + 1) = tm.step (tm.runFrom c j) := Function.iterate_succ_apply' _ _ _

private theorem equivPreload (u suffix : List Bool) (hu : u.length = 4224)
    (j : ℕ) (hj : j ≤ 4224) :
    tm.runFrom (tm.initCfg (u ++ suffix)) (1+j) = loadCfg u suffix j := by
  induction j with
  | zero =>
    change tm.step _ = _
    rw [tm.step_of_state (q := .inr .start) rfl, tm, MultiTapeTM.tr_ofTr]
    refine Cfg.ext rfl (by rfl) ?_ rfl rfl
    funext i
    simp [loadCfg, scanCfg, tr, act, Action.apply, MultiTapeNTM.initCfg, Cfg.init]
    rw [show tapeOfList [true] = Function.update (fun _ : ℤ => (none : Option Bool)) 0 (some true) by
      simpa using tapeOfList_append_single ([] : List Bool) true]
  | succ j ih =>
    rw [show 1 + (j+1) = (1+j)+1 by omega, addTick, ih (by omega)]
    have hj' : j < u.length := by omega
    have hj'' : j ≤ (u ++ suffix).length := by simp; omega
    have hi : (loadCfg u suffix j).inputSymbol = some u[j] := by
      rw [inputSymbolInner j (by simp [loadCfg, scanCfg]; omega) (by simp; omega)]
      rw [List.getElem_append_left hj']
    have hs : (loadCfg u suffix j).state = some (.inl ⟨j, by omega⟩) := by
      simp [loadCfg, loadState, show j < 4224 by omega]
    rw [tm.step_of_state hs, tm, MultiTapeTM.tr_ofTr, hi]
    change (act (some (loadState (j+1))) 1 1 (some u[j]) _).apply _ = _
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext
      have hn : j+1 ≤ (u ++ suffix).length := by simp; omega
      have slide (n k : ℕ) (hk : k+1 ≤ n) :
          (moveInputPos (⟨min k n + 1, by omega⟩ : Fin (n+2)) 1).val = min (k+1) n + 1 := by
        simp [moveInputPos, min_eq_left (show k ≤ n by omega), min_eq_left hk,
          SignType.cast, show (k : ℤ)+1+1 < (n : ℤ)+2 by omega]
        omega
      exact slide _ _ hn
    · funext i
      have cap : (u.take j).length = j := by simp [min_eq_left (Nat.le_of_lt hj')]
      have wr : tapeOfList (true :: u.take (j+1)) =
          Function.update (tapeOfList (true :: u.take j)) ((j : ℤ)+1) (some u[j]) := by
        rw [List.take_succ_eq_append_getElem hj']
        change tapeOfList ((true :: u.take j) ++ [u[j]]) = _
        rw [tapeOfList_append_single]
        simp [cap]
      by_cases hi : i = 0
      · simp [act, Action.apply, loadCfg, scanCfg, hi, wr]
      · by_cases small : j < 128
        · have h0 : min j 128 = j := min_eq_left (by omega)
          have h1 : min (j+1) 128 = j+1 := min_eq_left (by omega)
          simp [act, Action.apply, loadCfg, scanCfg, small, h0, wr]
        · have h0 : min j 128 = 128 := min_eq_right (by omega)
          have h1 : min (j+1) 128 = 128 := min_eq_right (by omega)
          simp [act, Action.apply, loadCfg, scanCfg, hi, small, h0, h1]
    · funext i
      simp [act, Action.apply, loadCfg, scanCfg]

private theorem goesHome (x cert hist : List Bool) (p j : ℕ) (hj : j ≤ cert.length) :
    tm.runFrom (scanCfg x cert hist p ((j : ℤ)-1) .home) (j+1) =
      scanCfg x cert hist p 0 .first := by
  induction j with
  | zero =>
    change tm.step _ = _
    rw [tm.step_of_state (q := .inr .home) rfl, tm, MultiTapeTM.tr_ofTr]
    simp only [Nat.cast_zero]
    have ht : tr (.inr .home) (scanCfg x cert hist p ((0:ℤ)-1) .home).inputSymbol
        (scanCfg x cert hist p ((0:ℤ)-1) .home).workTapeSymbols = go .first 0 1 := by rfl
    rw [ht]
    refine Cfg.ext rfl (by simp [go, act, Action.apply, scanCfg]) ?_ rfl rfl
    funext i; simp [go, act, Action.apply, scanCfg]
  | succ j ih =>
    rw [show tm.runFrom (scanCfg x cert hist p (((j+1 : ℕ):ℤ)-1) .home) (j+1+1) =
        tm.runFrom (tm.step _) (j+1) by rfl]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [tm.step_of_state (q := .inr .home) rfl, tm, MultiTapeTM.tr_ofTr]
    have ht : tr (.inr .home) (scanCfg x cert hist p j .home).inputSymbol
        (scanCfg x cert hist p j .home).workTapeSymbols = go .home 0 (-1) := by
      simp [tr, Cfg.workTapeSymbols, scanCfg, show j < cert.length by omega]
    rw [ht]
    apply Eq.trans _ (ih (by omega))
    congr 1
    refine Cfg.ext rfl (by simp [go, act, Action.apply, scanCfg]) ?_ rfl rfl
    funext i; simp [go, act, Action.apply, scanCfg]

private theorem setupCorrect (u suffix : List Bool) (hu : u.length = 4224) :
    tm.runFrom (tm.initCfg (u ++ suffix)) 8452 =
      scanCfg (u ++ suffix) (true :: u) (true :: u.take 128) 4224 0 .first := by
  have load := equivPreload u suffix hu 4224 le_rfl
  have hcfg : loadCfg u suffix 4224 =
      scanCfg (u ++ suffix) (true :: u) (true :: u.take 128) 4224 4225 .turn := by
    simp [loadCfg, loadState, List.take_of_length_le (show u.length ≤ 4224 by omega)]
    rfl
  rw [hcfg] at load
  have turn : tm.step (scanCfg (u ++ suffix) (true :: u) (true :: u.take 128) 4224 4225 .turn) =
      scanCfg (u ++ suffix) (true :: u) (true :: u.take 128) 4224 4224 .home := by
    rw [tm.step_of_state (q := .inr .turn) rfl, tm, MultiTapeTM.tr_ofTr]
    refine Cfg.ext rfl (by simp [tr, go, act, Action.apply, scanCfg]) ?_ rfl rfl
    funext i; simp [tr, go, act, Action.apply, scanCfg]
  have back := goesHome (u ++ suffix) (true :: u) (true :: u.take 128) 4224 4225 (by simp [hu])
  rw [show (8452 : ℕ) = 4226+4226 by decide]
  change tm.step^[4226+4226] _ = _
  rw [Function.iterate_add_apply]
  change tm.runFrom (tm.runFrom _ (4225+1)) 4226 = _
  rw [addTick (tm.initCfg _) 4225, load, turn]
  exact back

private theorem seqRun {x : List Bool} (c : Cfg 2 Bool State x) (n m : ℕ) :
    tm.runFrom c (n+m) = tm.runFrom (tm.runFrom c n) m := by
  unfold MultiTapeTM.runFrom
  rw [Nat.add_comm n m, Function.iterate_add_apply]

private theorem nextCycle (x cert hist : List Bool) (p : ℕ) (v : Bool)
    (hlt : hist.length < cert.length) :
    tm.runFrom (scanCfg x cert hist p hist.length (.advance v)) (hist.length + 2) =
      scanCfg x cert hist p 0 .first := by
  have hstep : tm.step (scanCfg x cert hist p hist.length (.advance v)) =
      scanCfg x cert hist p ((hist.length : ℤ)-1) .home := by
    rw [tm.step_of_state (q := .inr (.advance v)) rfl, tm, MultiTapeTM.tr_ofTr]
    have ht : tr (.inr (.advance v)) (scanCfg x cert hist p hist.length (.advance v)).inputSymbol
        (scanCfg x cert hist p hist.length (.advance v)).workTapeSymbols = go .home 0 (-1) := by
      simp [tr, Cfg.workTapeSymbols, scanCfg, hlt]
    rw [ht]
    refine Cfg.ext rfl (by simp [go, act, Action.apply, scanCfg]) ?_ rfl rfl
    funext i; simp [go, act, Action.apply, scanCfg]
  change tm.runFrom (tm.step _) (hist.length+1) = _
  rw [hstep]
  apply goesHome _ _ _ _ _ (by omega)

private theorem lastStop (x cert hist : List Bool) (v : Bool) (hlen : hist.length = cert.length) :
    (tm.step (scanCfg x cert hist x.length hist.length (.advance v))).state = none ∧
    (tm.step (scanCfg x cert hist x.length hist.length (.advance v))).output = [v] := by
  have hi : (scanCfg x cert hist x.length hist.length (.advance v)).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [scanCfg]))
  rw [tm.step_of_state (q := .inr (.advance v)) rfl, tm, MultiTapeTM.tr_ofTr, hi]
  simp [tr, Cfg.workTapeSymbols, scanCfg, hlen, finish, act, Action.apply]

private theorem foldPrefix (h : List Bool) (b : Bool) (gs : GateList) :
    ∃ tail, (gs.foldl estep (h,b)).1 = h ++ tail := by
  induction gs generalizing h b with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    let v := !(h.getD g.1 true && h.getD g.2 true)
    obtain ⟨t,ht⟩ := ih (h++[v]) v
    exact ⟨v::t, ht.trans (by simp)⟩

set_option maxRecDepth 20000 in
private theorem runGates (gs : GateList) (cert hist : List Bool) (last : Bool)
    (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (hx : x.drop p = encGates gs)
    (hg : gs ≠ []) (hc : cert.length = 4225) (hlen : hist.length + gs.length = 4225)
    (pre : ∃ t, cert = hist ++ t)
    (valid : ∀ g ∈ gs, g.1 < 4225 ∧ g.2 < 4225) :
    ∃ t ≤ gs.length * 42250,
      let res := tm.runFrom (scanCfg x cert hist p 0 .first) t
      let f := gs.foldl estep (hist,last)
      res.state = none ∧ res.output = [decide (f.1 = cert) && f.2] := by
  induction gs generalizing hist last p with
  | nil => contradiction
  | cons g gs ih =>
    obtain ⟨a,b⟩ := g
    let v := !(hist.getD a true && hist.getD b true)
    let u := MultiTapeTM.frame (encGate (a,b))
    let q := p + u.length
    let t₁ := 5*a + 3*b + 5
    let t₂ := hist.length+1
    have hValid := valid (a,b) (by simp)
    have ha : a < 4225 := hValid.1
    have hb : b < 4225 := hValid.2
    have hw : x.drop p = u ++ encGates gs := hx
    have hq : q ≤ x.length := by
      have e := congrArg List.length hw
      simp only [List.length_drop, List.length_append] at e
      dsimp [q]; omega
    have hrest : x.drop q = encGates gs := by
      simpa [q, List.drop_drop] using congrArg (List.drop u.length) hw
    have hlook : tm.runFrom (scanCfg x cert hist p 0 .first) t₁ =
        scanCfg x cert hist q 0 (.appendBit v) :=
      lookup_block cert hist a b (by omega) (by omega) x p _ hp hw
    have hstep : ((a,b)::gs).foldl estep (hist,last) = gs.foldl estep (hist++[v],v) := rfl
    have hlim : hist.length ≤ 4224 := by simp at hlen; omega
    have hcount : ((a,b)::gs).length * 42250 = gs.length * 42250 + 42250 := by
      simp [Nat.succ_mul]
    have tick1 : t₁+t₂ ≤ 42250 := by dsimp [t₁,t₂]; omega
    by_cases hm : cert[hist.length]? = some v
    · have hcommit := commit_block x cert hist q v
      rw [if_pos hm] at hcommit
      let hist' := hist ++ [v]
      have hBoth : tm.runFrom (scanCfg x cert hist p 0 .first) (t₁+t₂) =
          scanCfg x cert hist' q hist'.length (.advance v) := by
        rw [seqRun, hlook]
        simpa [hist',t₂] using hcommit
      obtain ⟨tail,htail⟩ := pre
      have headEq : tail[0]? = some v := by
        simpa [htail, List.getElem?_append_right] using hm
      cases tail with
      | nil => simp at headEq
      | cons b' tail =>
        have eq : b' = v := by simpa using headEq
        subst b'
        have post : cert = hist' ++ tail := by simpa [hist'] using htail
        cases gs with
        | nil =>
          have eqcert : cert = hist' := by
            have := congrArg List.length post
            simp [hist'] at this hlen
            have htail0 : tail.length = 0 := by omega
            simpa [List.length_eq_zero_iff.mp htail0] using post
          have qEnd : q = x.length := by
            have e := congrArg List.length hrest
            simp at e
            omega
          have fin := lastStop x cert hist' v (by rw [eqcert])
          refine ⟨t₁+t₂+1, ?_, ?_⟩
          · dsimp [t₁,t₂]; simp; omega
          · rw [addTick, hBoth, qEnd]
            simpa [hstep, eqcert, hist'] using fin
        | cons g rest =>
          have hlen' : hist'.length + (g::rest).length = 4225 := by simpa [hist', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
          obtain ⟨t,ht,hRun⟩ := ih hist' v q hq hrest (by simp) hlen' ⟨tail,post⟩
            (fun g' h' => valid g' (by simp [h']))
          have next := nextCycle x cert hist' q v (by simp at hlen'; omega)
          refine ⟨(t₁+t₂)+(hist'.length+2)+t, ?_, ?_⟩
          · rw [hcount, Nat.add_comm (_ * _) 42250]
            apply Nat.add_le_add _ ht
            dsimp [hist',t₁,t₂]
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [seqRun _ ((t₁+t₂)+(hist'.length+2)) t, seqRun _ (t₁+t₂) _, hBoth, next, hstep]
            exact hRun
    · have fail := commit_block x cert hist q v
      rw [if_neg hm] at fail
      have ne : (gs.foldl estep (hist++[v],v)).1 ≠ cert := by
        obtain ⟨tail, ht⟩ := foldPrefix (hist++[v]) v gs
        intro eq
        apply hm
        rw [← eq, ht]
        simp [List.append_assoc]
      refine ⟨t₁+t₂, by rw [hcount]; omega, ?_⟩
      rw [seqRun, hlook, show t₂ = hist.length+1 from rfl, fail, hstep]
      simp [ne]

set_option maxRecDepth 20000 in
theorem solution (x : Fin 128 → Bool) (t : Fin 4096 → Bool) (φ : CircuitSAT.Circuit 128 4096) :
    machine.run (word x t φ) = PMF.pure
      [decide (List.ofFn t = trace (List.ofFn x) φ.gates) && evalGates (List.ofFn x, φ.gates)] := by
  let xs := List.ofFn x
  let ts := List.ofFn t
  let u := xs ++ ts
  let input := u ++ encGates φ.gates
  let cert := true :: u
  let hist := true :: xs
  let gs := φ.gates
  have hxs : xs.length = 128 := List.length_ofFn
  have hts : ts.length = 4096 := List.length_ofFn
  have hu : u.length = 4224 := by simp [u,hxs,hts]
  have hg : gs.length = 4096 := List.length_ofFn
  have setup : tm.runFrom (tm.initCfg input) 8452 = scanCfg input cert hist 4224 0 .first := by
    have ht : u.take 128 = xs := by rw [← hxs]; exact List.take_left
    simpa only [ht] using setupCorrect u (encGates gs) hu
  have hp : 4224 ≤ input.length := by change 4224 ≤ (u ++ encGates gs).length; simp [hu]
  have hx : input.drop 4224 = encGates gs := by
    change (u ++ encGates gs).drop 4224 = encGates gs
    rw [← hu, List.drop_left]
  have hvalid : ∀ g ∈ gs, g.1 < 4225 ∧ g.2 < 4225 := by
    intro g hmem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact ⟨(φ i).1.isLt,(φ i).2.isLt⟩
  obtain ⟨j,hj,halt,out⟩ := runGates gs cert hist true input 4224 hp hx
    (by intro hn; simp [hn] at hg) (by simp [cert,hu]) (by simp [hist,hxs,hg])
    ⟨ts,rfl⟩ hvalid
  have combo : tm.runFrom (tm.initCfg input) (8452+j) = tm.runFrom (scanCfg input cert hist 4224 0 .first) j := by
    rw [seqRun, setup]
  have lim : 8452+j ≤ clock := by rw [hg] at hj; dsimp [clock]; omega
  have actual := tm.runFrom_eq_of_halt (tm.initCfg input) lim (by rw [combo]; exact halt)
  rw [show word x t φ = input by simp only [word,input,u,xs,ts,List.append_assoc], machine, Machine.run_ofTM]
  change PMF.pure (tm.runFrom (tm.initCfg input) clock).output = _
  rw [actual, combo, out]
  obtain ⟨gatesOut,histEq⟩ := foldPrefix hist true gs
  change PMF.pure [decide ((gs.foldl estep (hist,true)).1 = cert) && (gs.foldl estep (hist,true)).2] =
    PMF.pure [decide (ts = (gs.foldl estep (hist,true)).1.drop (xs.length + 1)) &&
      (gs.foldl estep (hist,true)).2]
  rw [histEq]
  have cut : (hist ++ gatesOut).drop (xs.length+1) = gatesOut := by
    change (hist ++ gatesOut).drop hist.length = _
    exact List.drop_left
  rw [cut, show cert = hist ++ ts from rfl]
  simp [eq_comm]
