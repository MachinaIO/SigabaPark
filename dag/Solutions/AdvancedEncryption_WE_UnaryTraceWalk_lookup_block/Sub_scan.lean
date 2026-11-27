import Definitions.Def_WE_UnaryTraceBlocks

open Turing SigabaNeo AdvancedEncryption.WE.UnaryTraceWalk

private theorem sequenceBlocks {c h : List Bool} {s m e : Phase} {u v w : ℤ}
    {a b : List Bool} {n k : ℕ}
    (ha : Scans c h s u a n m v) (hb : Scans c h m v b k e w) :
    Scans c h s u (a ++ b) (n + k) e w := by
  intro x p tail hp hx
  have hl := congrArg List.length hx
  simp only [List.length_drop, List.length_append] at hl
  have hx' : x.drop (p + a.length) = b ++ tail := by
    simpa [List.drop_drop, List.append_assoc] using congrArg (List.drop a.length)
      (show x.drop p = a ++ (b ++ tail) by simpa [List.append_assoc] using hx)
  rw [show tm.runFrom (scanCfg x c h p u s) (n + k) =
      tm.runFrom (tm.runFrom (scanCfg x c h p u s) n) k by
        unfold MultiTapeTM.runFrom
        rw [Nat.add_comm n k, Function.iterate_add_apply]]
  rw [ha x p (b ++ tail) hp (by simpa [List.append_assoc] using hx)]
  simpa [Nat.add_assoc] using hb x (p + a.length) tail (by omega) hx'

private theorem noop (c h : List Bool) (s : Phase) (z : ℤ) : Scans c h s z [] 0 s z := by
  intro x p tail hp hx
  rfl

private def readWork (c h : List Bool) (z : ℤ) (i : Fin 2) :=
  tapeOfList (if i = 0 then c else h) z

private theorem readOne {c h : List Bool} {q r : Phase} {z : ℤ} {d : SignType} {b : Bool}
    (ht : tr (.inr q) (some b) (readWork c h z) = go r 1 d) :
    Scans c h q z [b] 1 r (z + (d : ℤ)) := by
  intro x p tail hp hx
  have hl := congrArg List.length hx
  simp at hl
  have hsym : (scanCfg x c h p z q).inputSymbol = some b := by
    rw [inputSymbolInner p (by simp [scanCfg, min_eq_left hp]; omega) (by omega)]
    have he := congrArg List.head? hx
    simpa [List.getElem?_eq_getElem (show p < x.length by omega)] using he
  change tm.step _ = _
  rw [tm.step_of_state (q := .inr q) rfl, hsym]
  change ((MultiTapeTM.ofTr _ tr).tr _ _ (readWork c h z)).apply _ = _
  rw [MultiTapeTM.tr_ofTr, ht]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    have hp' : p + 1 ≤ x.length := by omega
    change (moveInputPos _ 1).val = min (p + 1) x.length + 1
    simp [moveInputPos, scanCfg, min_eq_left hp, min_eq_left hp', SignType.cast,
      show (p : ℤ) + 1 + 1 < (x.length : ℤ) + 2 by omega]
    omega
  · funext i
    simp [Action.apply, go, act, scanCfg]
  · rfl

private theorem stayOne {c h : List Bool} {q r : Phase} {z : ℤ} {d : SignType}
    (ht : ∀ i, tr (.inr q) i (readWork c h z) = go r 0 d) :
    Scans c h q z [] 1 r (z + (d : ℤ)) := by
  intro x p tail hp hx
  change tm.step _ = _
  rw [tm.step_of_state (q := .inr q) rfl]
  change ((MultiTapeTM.ofTr _ tr).tr _ _ (readWork c h z)).apply _ = _
  rw [MultiTapeTM.tr_ofTr, ht]
  refine Cfg.ext rfl (by simp [Action.apply, go, act, scanCfg]) ?_ rfl rfl
  funext i
  simp [Action.apply, go, act, scanCfg]

private theorem repeatUnits {c h : List Bool} {s : Phase} {width : ℕ}
    (unit : ∀ (j : ℕ), j < c.length →
      Scans c h s j (List.replicate width true) width s (j + 1))
    (start count : ℕ) (bound : start + count ≤ c.length) :
    Scans c h s start (List.replicate (width * count) true) (width * count) s
      ((start + count : ℕ) : ℤ) := by
  induction count with
  | zero => simpa using noop c h s start
  | succ count ih =>
    have hseq := sequenceBlocks (ih (by omega))
      (unit (start + count) (by omega))
    rw [Nat.mul_succ, List.replicate_add]
    convert hseq using 1
    push_cast
    omega

private theorem rewind {c h : List Bool} {s r : Phase}
    (marked : ∀ (j : ℕ), j < c.length → ∀ i, tr (.inr s) i (readWork c h j) = go s 0 (-1))
    (blank : ∀ i, tr (.inr s) i (readWork c h (-1)) = go r 0 1)
    (j : ℕ) (hj : j ≤ c.length) :
    Scans c h s ((j : ℤ) - 1) [] (j + 1) r 0 := by
  induction j with
  | zero => simpa using stayOne blank
  | succ j ih =>
    have step : Scans c h s (j : ℤ) [] 1 s ((j : ℤ) - 1) := by
      simpa [sub_eq_add_neg] using stayOne (marked j (by omega))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      sequenceBlocks step (ih (by omega))

private theorem gateFrame (a b : ℕ) :
    MultiTapeTM.frame (encGate (a,b)) =
      List.replicate (4*a) true ++ [true,false] ++ List.replicate (2*b) true ++ [false] := by
  let f : Bool → List Bool := fun t => [true,t]
  have one (m : ℕ) : (List.replicate m true).flatMap f = List.replicate (2*m) true := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp [List.replicate_succ, ih, Nat.mul_succ, f]
  change MultiTapeTM.frame (MultiTapeTM.frame (List.replicate a true) ++ List.replicate b true) = _
  unfold MultiTapeTM.frame
  change (((List.replicate a true).flatMap f ++ [false]) ++ List.replicate b true).flatMap f ++ [false] = _
  simp only [List.flatMap_append, one]
  rw [show 2*(2*a) = 4*a by omega]
  simp [f, List.append_assoc]

private theorem firstUnit (c h : List Bool) (j : ℕ) (hj : j < c.length) :
    Scans c h .first j (List.replicate 4 true) 4 .first ((j : ℤ) + 1) := by
  have t1 : Scans c h .first (j : ℤ) [true] 1 .firstTag j := by
    simpa using readOne (d := 0) (by simp [tr, readWork, hj] : 
      tr (.inr .first) (some true) (readWork c h j) = go .firstTag 1 0)
  have t2 : Scans c h .firstTag (j : ℤ) [true] 1 .firstThird j := by
    simpa using readOne (d := 0) (by rfl : tr (.inr .firstTag) (some true)
      (readWork c h j) = go .firstThird 1 0)
  have t3 : Scans c h .firstThird (j : ℤ) [true] 1 .firstFourth j := by
    simpa using readOne (d := 0) (by rfl : tr (.inr .firstThird) (some true)
      (readWork c h j) = go .firstFourth 1 0)
  have t4 := readOne (by rfl : tr (.inr .firstFourth) (some true)
    (readWork c h j) = go .first 1 1)
  exact sequenceBlocks (sequenceBlocks (sequenceBlocks t1 t2) t3) t4

theorem solution (cert hist : List Bool) (a b : ℕ)
    (ha : a < cert.length) (hb : b < cert.length) :
    Scans cert hist .first 0 (Turing.MultiTapeTM.frame (SigabaNeo.encGate (a, b)))
      (5 * a + 3 * b + 5) (.appendBit (!(hist.getD a true && hist.getD b true))) 0 := by
  let A := hist.getD a true
  let B := hist.getD b true
  let v := !(A && B)
  have first := repeatUnits (firstUnit cert hist) 0 a (by omega)
  have tag : Scans cert hist .first (a : ℤ) [true] 1 .firstTag a := by
    simpa using readOne (by simp [tr, readWork, ha] :
      tr (.inr .first) (some true) (readWork cert hist a) = go .firstTag 1 0)
  have sep := readOne (by simp [A, tr, readWork, List.getD_eq_getElem?_getD] :
    tr (.inr .firstTag) (some false) (readWork cert hist a) = go (.homeSecond A) 1 (-1))
  have back := rewind (c := cert) (h := hist) (s := .homeSecond A) (r := .second A)
    (by intro j hj i; simp [tr, readWork, hj])
    (by intro i; rfl) a (by omega)
  have secondOne (j : ℕ) (hj : j < cert.length) :
      Scans cert hist (.second A) j (List.replicate 2 true) 2 (.second A) ((j : ℤ) + 1) := by
    have hd : Scans cert hist (.second A) j [true] 1 (.secondPair A) j := by
      simpa using readOne (by simp [tr, readWork, hj] :
        tr (.inr (.second A)) (some true) (readWork cert hist j) = go (.secondPair A) 1 0)
    exact sequenceBlocks hd (readOne (by rfl : tr (.inr (.secondPair A)) (some true)
      (readWork cert hist j) = go (.second A) 1 1))
  have second := repeatUnits secondOne 0 b (by omega)
  have endB := readOne (by simp [v, B, tr, readWork, hb, List.getD_eq_getElem?_getD] :
    tr (.inr (.second A)) (some false) (readWork cert hist b) = go (.homeAppend v) 1 (-1))
  have reset := rewind (c := cert) (h := hist) (s := .homeAppend v) (r := .appendBit v)
    (by intro j hj i; simp [tr, readWork, hj])
    (by intro i; rfl) b (by omega)
  simp only [Nat.zero_add, Nat.cast_zero] at first second
  have moves := sequenceBlocks (sequenceBlocks (sequenceBlocks (sequenceBlocks
    (sequenceBlocks (sequenceBlocks first tag) sep) back) second) endB) reset
  rw [gateFrame]
  have tickEq : 5*a + 3*b + 5 = 4*a+1+1+(a+1)+2*b+1+(b+1) := by omega
  rw [tickEq]
  simpa [v, A, B, List.append_assoc] using moves
