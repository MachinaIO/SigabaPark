import Definitions.Def_WE_TraceEmitterStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

open Turing SigabaNeo AdvancedEncryption.WE.TraceEmitter

private inductive Route where | par | stmt | wit

private def Route.tag : Route → Phase
  | .par => .params | .stmt => .statement | .wit => .witness
private def Route.data : Route → Phase
  | .par => .paramsData | .stmt => .statementData | .wit => .witnessData
private def Route.last : Route → Phase
  | .par => .statement | .stmt => .witness | .wit => .rewindStatement
private def Route.swrite : Route → Option Bool → Option Bool
  | .stmt, b => b | _, _ => none
private def Route.hwrite : Route → Option Bool → Option Bool
  | .wit, b => b | _, _ => none
private def Route.smove : Route → SignType
  | .stmt => 1 | _ => 0
private def Route.hmove : Route → SignType
  | .wit => 1 | _ => 0
private def Route.finishMove : Route → SignType
  | .wit => -1 | _ => 0
private def Route.sadd : Route → List Bool → List Bool
  | .stmt, l => l | _, _ => []
private def Route.hadd : Route → List Bool → List Bool
  | .wit, l => l | _, _ => []
private theorem framed (m : Route) (u : List Bool) (x : List Bool) (p : ℕ) (s h tail : List Bool)
    (hp : p ≤ x.length) (hx : x.drop p = MultiTapeTM.frame u ++ tail) :
    tm.runFrom (snap x p s h s.length h.length (some m.tag)) (2 * u.length + 1) =
      snap x (p+2*u.length+1) (s ++ m.sadd u) (h ++ m.hadd u)
        ((s ++ m.sadd u).length + m.finishMove.cast)
        (h ++ m.hadd u).length (some m.last) := by
  induction u generalizing p s h with
  | nil =>
    have hh := congrArg List.head? hx
    have sym : x[p]? = some false := by simpa [MultiTapeTM.frame] using hh
    have hl : p < x.length := by
      by_contra! h
      simp [List.getElem?_eq_none h] at sym
    change tm.step _ = _
    have t := tick (q := m.tag) (q' := some m.last) (move := true)
      (ds := m.finishMove) (dh := 0) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := (s.length : ℤ)) (j := (h.length : ℤ))
      (out := []) (by exact hl) (by cases m <;> simp [sym, tr, Route.tag, Route.last, Route.finishMove])
      (by simp) (by simp)
    cases m <;> simpa [Route.sadd, Route.hadd, Route.tag, Route.last, Route.finishMove,
      appendOption] using t
  | cons b u ih =>
    have q : x.drop p = true :: b :: (MultiTapeTM.frame u ++ tail) := by
      simpa [MultiTapeTM.frame] using hx
    have len := congrArg List.length q
    simp only [List.length_drop, List.length_cons, List.length_append] at len
    have ht : x[p]? = some true := by simpa using congrArg List.head? q
    have q1 : x.drop (p+1) = b :: (MultiTapeTM.frame u ++ tail) := by
      simpa [List.drop_drop] using congrArg (List.drop 1) q
    have hb : x[p+1]? = some b := by simpa using congrArg List.head? q1
    have q2 : x.drop (p+2) = MultiTapeTM.frame u ++ tail := by
      simpa [List.drop_drop] using congrArg (List.drop 2) q
    have t1 := tick (q := m.tag) (q' := some m.data) (move := true)
      (ds := 0) (dh := 0) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := (s.length : ℤ)) (j := (h.length : ℤ))
      (out := []) (by change p+1 ≤ x.length; omega)
      (by cases m <;> simp [ht, tr, Route.tag, Route.data]) (by simp) (by simp)
    have t2 := tick (q := m.data) (q' := some m.tag) (move := true)
      (ds := m.smove) (dh := m.hmove) (sw := m.swrite (some b))
      (hw := m.hwrite (some b)) (emit := none)
      (x := x) (p := p+1) (s := s) (h := h) (z := (s.length : ℤ)) (j := (h.length : ℤ))
      (out := []) (by change p+1+1 ≤ x.length; omega)
      (by cases m <;> simp [hb, tr, Route.tag, Route.data, Route.swrite, Route.hwrite,
        Route.smove, Route.hmove]) (by simp) (by simp)
    have rest := ih (p+2) (s ++ m.sadd [b]) (h ++ m.hadd [b]) (by omega) q2
    rw [show 2*(b::u).length+1 = (2*u.length+1)+1+1 by simp; omega]
    change tm.runFrom (tm.step (tm.step _)) (2*u.length+1) = _
    simp [appendOption] at t1
    rw [t1, t2]
    cases m <;> simpa [appendOption, Route.sadd, Route.hadd, Route.tag, Route.smove,
      Route.hmove, Route.finishMove, Route.swrite, Route.hwrite, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_add, Int.add_assoc] using rest

private theorem advance {x : List Bool} {start mid finish : Cfg 3 Bool Phase x} {a b : ℕ}
    (ha : tm.runFrom start a = mid) (hb : tm.runFrom mid b = finish) :
    tm.runFrom start (a+b) = finish := by
  rw [show tm.runFrom start (a+b) = tm.runFrom (tm.runFrom start a) b by
    unfold MultiTapeTM.runFrom
    rw [Nat.add_comm a b, Function.iterate_add_apply], ha, hb]

private theorem origin (j : ℕ) : (tapeOfList [true] (j : ℤ)).isSome = decide (j = 0) := by
  cases j <;> rfl

private theorem rewindS (x s h : List Bool) (p k : ℕ) (j : ℤ)
    (hp : p ≤ x.length) (hk : k ≤ s.length) :
    tm.runFrom (snap x p s h ((k : ℤ)-1) j (some .rewindStatement)) (k+1) =
      snap x p s h 0 j (some .rewindWitness) := by
  induction k with
  | zero =>
    have t := tick (q := .rewindStatement) (q' := some .rewindWitness) (move := false)
      (ds := 1) (dh := 0) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := -1) (j := j) (out := [])
      (by simpa) (by rfl) (by simp) (by simp)
    change tm.step _ = _
    simpa [appendOption] using t
  | succ k ih =>
    have someCell : (tapeOfList s (k : ℤ)).isSome = true := by simp; omega
    have t := tick (q := .rewindStatement) (q' := some .rewindStatement) (move := false)
      (ds := -1) (dh := 0) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := k) (j := j) (out := [])
      (by simpa) (by simp [tr, show k < s.length by omega]) (by simp) (by simp)
    have one : tm.step (snap x p s h k j (some .rewindStatement)) =
        snap x p s h ((k : ℤ)-1) j (some .rewindStatement) := by
      simpa [appendOption, sub_eq_add_neg] using t
    change tm.runFrom (tm.step _) (k+1) = _
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [one, ih (by omega)]
private theorem rewindH (x s h : List Bool) (p j : ℕ) (hp : p ≤ x.length) :
    tm.runFrom (snap x p s h 0 j (some .rewindWitness)) (j+1) =
      snap x p s h 0 0 (some .first) := by
  induction j with
  | zero =>
    have t := tick (q := .rewindWitness) (q' := some .first) (move := false)
      (ds := 0) (dh := 0) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := 0) (j := 0) (out := [])
      (by simpa) (by rfl) (by simp) (by simp)
    change tm.step _ = _
    simpa [appendOption] using t
  | succ j ih =>
    have t := tick (q := .rewindWitness) (q' := some .rewindWitness) (move := false)
      (ds := 0) (dh := -1) (sw := none) (hw := none) (emit := none)
      (x := x) (p := p) (s := s) (h := h) (z := 0) (j := ((j+1 : ℕ) : ℤ)) (out := [])
      (by simpa) (by have hz : tapeOfList [true] ((j+1 : ℕ):ℤ) = none := by rfl
                     simp only [tr, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, hz]; rfl) (by simp) (by simp)
    have one : tm.step (snap x p s h 0 ((j+1 : ℕ):ℤ) (some .rewindWitness)) =
        snap x p s h 0 j (some .rewindWitness) := by
      simpa [appendOption] using t
    change tm.runFrom (tm.step _) (j+1) = _
    rw [one, ih]

private theorem init (x : List Bool) :
    tm.step (tm.initCfg x) = snap x 0 [] [true] 0 1 (some .params) := by
  rw [tm.step_of_state (q := .init) rfl, tm, MultiTapeTM.tr_ofTr]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext t
    have wr : tapeOfList [true] = Function.update (fun _ : ℤ ↦ none) 0 (some true) := by
      simpa using tapeOfList_append_single ([] : List Bool) true
    by_cases a : t = 0 <;> by_cases b : t = 1 <;>
      simp [Action.apply, tr, action, MultiTapeNTM.initCfg, Cfg.init, snap, a, b, wr]
  · funext t
    by_cases a : t = 0 <;> by_cases b : t = 1 <;>
      simp [Action.apply, tr, action, MultiTapeNTM.initCfg, Cfg.init, snap, a, b]

theorem solution (params stmt wit tail : List Bool) :
    let x := MultiTapeTM.frame params ++ MultiTapeTM.frame stmt ++ MultiTapeTM.frame wit ++ tail
    let off := 2*params.length + 2*stmt.length + 2*wit.length + 3
    tm.runFrom (tm.initCfg x) (2*params.length + 3*stmt.length + 3*wit.length + 7) =
      snap x off stmt (true :: wit) 0 0 (some .first) := by
  dsimp only
  let x := MultiTapeTM.frame params ++ MultiTapeTM.frame stmt ++ MultiTapeTM.frame wit ++ tail
  let p := 2*params.length+1
  let k := p+2*stmt.length+1
  let e := k+2*wit.length+1
  have leq : e ≤ x.length := by simp [e,k,p,x,MultiTapeTM.length_frame]; omega
  have lp : x.drop p = MultiTapeTM.frame stmt ++ (MultiTapeTM.frame wit ++ tail) := by
    simp [p,x,List.append_assoc, ← MultiTapeTM.length_frame]
  have lk : x.drop k = MultiTapeTM.frame wit ++ tail := by
    rw [show k=p+(2*stmt.length+1) by dsimp [k]; omega, ← List.drop_drop, lp]
    simp [← MultiTapeTM.length_frame]
  have par := framed .par params x 0 [] [true] (MultiTapeTM.frame stmt ++ (MultiTapeTM.frame wit ++ tail)) (by omega)
    (show x.drop 0 = _ by simp [x,List.append_assoc])
  have st := framed .stmt stmt x p [] [true] _ (by dsimp [e,k] at leq; omega) lp
  have wi := framed .wit wit x k stmt [true] _ (by dsimp [e] at leq; omega) lk
  simp [Route.tag,Route.last,Route.sadd,Route.hadd,Route.finishMove] at par st wi
  have first : tm.runFrom (tm.initCfg x) 1 = snap x 0 [] [true] 0 1 (some .params) := init x
  have h1 := advance first par
  have h2 := advance h1 st
  have h3 := advance h2 wi
  have h4 := advance h3 (rewindS x stmt (true::wit) e stmt.length (wit.length+1) leq le_rfl)
  have h5 := advance h4 (rewindH x stmt (true::wit) e (wit.length+1) leq)
  convert h5 using 1 <;> dsimp [e,k,p,x] <;> congr 1 <;> omega
