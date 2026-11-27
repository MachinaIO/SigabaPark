import Definitions.Def_WE_TraceEmitterStep
import SigabaNeoStd.Machines.Gates

open Turing SigabaNeo AdvancedEncryption.WE.TraceEmitter

private def Walk (h : List Bool) (q : Phase) (j : ℤ) (bits : List Bool) (n : ℕ)
    (r : Phase) (y : ℤ) : Prop :=
  ∀ (x : List Bool) (p : ℕ) (s : List Bool) (k : ℕ) (tail out : List Bool),
    p ≤ x.length → k ≤ s.length → s.drop k = bits ++ tail →
    tm.runFrom (snap x p s h k j (some q) out) n =
      snap x p s h ((k+bits.length : ℕ):ℤ) y (some r) out

private theorem seq {h : List Bool} {q m r : Phase} {j u v : ℤ} {a b : List Bool}
    {n l : ℕ} (ha : Walk h q j a n m u) (hb : Walk h m u b l r v) :
    Walk h q j (a++b) (n+l) r v := by
  intro x p s k tail out hp hk hs
  have len := congrArg List.length hs
  simp only [List.length_append, List.length_drop] at len
  have hx := ha x p s k (b++tail) out hp hk (by simpa [List.append_assoc] using hs)
  have hy := hb x p s (k+a.length) tail out hp (by omega) (by
    simpa [List.drop_drop, List.append_assoc] using congrArg (List.drop a.length)
      (show s.drop k = a ++ (b ++ tail) by simpa [List.append_assoc] using hs))
  rw [show tm.runFrom (snap x p s h k j (some q) out) (n+l) =
       tm.runFrom (tm.runFrom (snap x p s h k j (some q) out) n) l by
        unfold MultiTapeTM.runFrom
        rw [Nat.add_comm n l, Function.iterate_add_apply], hx]
  simpa [Nat.add_assoc] using hy

private def heads (a b c : Option Bool) (t : Fin 3) := if t=0 then a else if t=1 then b else c

private theorem readOne {h : List Bool} {q r : Phase} {j : ℤ} {d : SignType} {b : Bool}
    (ht : ∀ i, tr q i (heads (some b) (tapeOfList h j) (tapeOfList [true] j)) =
        action (some r) 0 1 d) :
    Walk h q j [b] 1 r (j+d.cast) := by
  intro x p s k tail out hp hk hs
  have hb : s[k]? = some b := by simpa using congrArg List.head? hs
  have t := tick (x := x) (p := p) (s := s) (h := h) (z := k) (j := j) (q := q)
    (out := out) (move := false) (ds := 1) (dh := d) (sw := none) (hw := none) (emit := none)
    (q' := some r) (by simpa) (by rw [tapeOfList_ofNat, hb]; exact ht _) (by simp) (by simp)
  change tm.step _ = _
  simpa [appendOption] using t

private theorem stay {h : List Bool} {q r : Phase} {j : ℤ} {d : SignType}
    (ht : ∀ i sym, tr q i (heads sym (tapeOfList h j) (tapeOfList [true] j)) =
        action (some r) 0 0 d) :
    Walk h q j [] 1 r (j+d.cast) := by
  intro x p s k tail out hp hk hs
  have t := tick (x := x) (p := p) (s := s) (h := h) (z := k) (j := j) (q := q)
    (out := out) (move := false) (ds := 0) (dh := d) (sw := none) (hw := none) (emit := none)
    (q' := some r) (by simpa) (by exact ht _ _) (by simp) (by simp)
  change tm.step _ = _
  simpa [appendOption] using t

private theorem units {h : List Bool} {q : Phase} {width : ℕ}
    (one : ∀ j : ℕ, Walk h q j (List.replicate width true) width q ((j:ℤ)+1))
    (start count : ℕ) : Walk h q start (List.replicate (width*count) true)
        (width*count) q ((start+count:ℕ):ℤ) := by
  induction count with
  | zero => intro x p s k tail out hp hk hs; simp [MultiTapeTM.runFrom]
  | succ n ih =>
    have H := seq ih (one (start+n))
    rw [Nat.mul_succ, List.replicate_add]
    convert H using 1
    push_cast
    omega

private theorem rewind {h : List Bool} {q r : Phase}
    (origin : ∀ i sym, tr q i (heads sym (tapeOfList h 0) (some true)) =
        action (some r) 0 0 0)
    (left : ∀ i sym val, tr q i (heads sym val none) = action (some q) 0 0 (-1))
    (j : ℕ) : Walk h q j [] (j+1) r 0 := by
  induction j with
  | zero => simpa using (stay (j := 0) (d := 0) (by exact origin) : Walk h q 0 [] 1 r _)
  | succ j ih =>
    have t : Walk h q ((j+1:ℕ):ℤ) [] 1 q j := by
      have e : tapeOfList [true] ((j+1:ℕ):ℤ) = none := by rfl
      simpa using (stay (j := ((j+1:ℕ):ℤ)) (d := -1)
        (by rw [e]; exact fun i sym ↦ left i sym _) : Walk h q _ [] 1 q _)
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using seq t ih

private theorem gateFrame (a b : ℕ) :
    MultiTapeTM.frame (encGate (a,b)) =
      List.replicate (4*a) true ++ [true,false] ++ List.replicate (2*b) true ++ [false] := by
  let f : Bool → List Bool := fun t => [true,t]
  have one (m : ℕ) : (List.replicate m true).flatMap f = List.replicate (2*m) true := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, ih, Nat.mul_succ, f]
  change MultiTapeTM.frame (MultiTapeTM.frame (List.replicate a true) ++ List.replicate b true) = _
  unfold MultiTapeTM.frame
  change (((List.replicate a true).flatMap f ++ [false]) ++ List.replicate b true).flatMap f ++ [false] = _
  simp only [List.flatMap_append, one]
  rw [show 2*(2*a) = 4*a by omega]
  simp [f, List.append_assoc]

private theorem look (h : List Bool) (a b : ℕ) :
    Walk h .first 0 (MultiTapeTM.frame (encGate (a,b))) (5*a+3*b+5)
      (.appendBit (!(h.getD a true && h.getD b true))) 0 := by
  let A := h.getD a true
  let v := !(A && h.getD b true)
  have firstUnit (j : ℕ) : Walk h .first j (List.replicate 4 true) 4 .first ((j:ℤ)+1) := by
    have h1 : Walk h .first j [true] 1 .firstTag j := by
      simpa using readOne (d := 0) (by intro i; rfl)
    have h2 : Walk h .firstTag j [true] 1 .firstThird j := by
      simpa using readOne (d := 0) (by intro i; rfl)
    have h3 : Walk h .firstThird j [true] 1 .firstFourth j := by
      simpa using readOne (d := 0) (by intro i; rfl)
    exact seq (seq (seq h1 h2) h3) (readOne (d := 1) (by intro i; rfl))
  have h1 := units firstUnit 0 a
  have tag : Walk h .first a [true] 1 .firstTag a := by
    simpa using readOne (d := 0) (by intro i; rfl)
  have sep : Walk h .firstTag a [false] 1 (.homeSecond A) a := by
    simpa using (readOne (h := h) (q := .firstTag) (r := .homeSecond A) (j := a) (b := false)
      (d := 0) (by intro i; simp [tr, heads, A, List.getD_eq_getElem?_getD]))
  have back := rewind (h := h) (q := .homeSecond A) (r := .second A)
    (by intros; rfl) (by intros; rfl) a
  have secUnit (j : ℕ) : Walk h (.second A) j (List.replicate 2 true) 2 (.second A) ((j:ℤ)+1) := by
    have hd : Walk h (.second A) j [true] 1 (.secondPair A) j := by
      simpa using readOne (d := 0) (by intro i; rfl)
    exact seq hd (readOne (d := 1) (by intro i; rfl))
  have second := units secUnit 0 b
  have endB : Walk h (.second A) b [false] 1 (.homeAppend v) b := by
    simpa using (readOne (h := h) (q := .second A) (r := .homeAppend v) (j := b) (b := false)
      (d := 0) (by intro i; simp [tr, heads, v, List.getD_eq_getElem?_getD]))
  have endBack := rewind (h := h) (q := .homeAppend v) (r := .appendBit v)
    (by intros; rfl) (by intros; rfl) b
  simp only [Nat.zero_add, Nat.cast_zero] at h1 second
  have all := seq (seq (seq (seq (seq (seq h1 tag) sep) back) second) endB) endBack
  rw [gateFrame, show 5*a+3*b+5 = 4*a+1+1+(a+1)+2*b+1+(b+1) by omega]
  simpa [A,v,List.append_assoc] using all

private theorem commit (h : List Bool) (v : Bool) (x : List Bool) (p : ℕ) (s out : List Bool)
    (k : ℕ) (hp : p ≤ x.length) (hk : k ≤ s.length) :
    tm.runFrom (snap x p s h k 0 (some (.appendBit v)) out) (2*h.length+3) =
      snap x p s (h++[v]) k 0 (some .first) (out++[true,v]) := by
  have walkFront (j : ℕ) (hj : j ≤ h.length) :
      tm.runFrom (snap x p s h k 0 (some (.appendBit v)) out) j =
      snap x p s h k j (some (.appendBit v)) out := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show tm.runFrom (snap x p s h k 0 (some (.appendBit v)) out) (j+1) =
          tm.step (tm.runFrom (snap x p s h k 0 (some (.appendBit v)) out) j) from
          Function.iterate_succ_apply' _ _ _, ih (by omega)]
      have t := tick (x := x) (p := p) (s := s) (h := h) (z := k) (j := j)
        (q := .appendBit v) (q' := some (.appendBit v)) (ds := 0) (dh := 1) (move := false)
        (out := out) (sw := none) (hw := none) (emit := none) (by simpa)
        (by simp [tr, show j < h.length by omega]) (by simp) (by simp)
      simpa [appendOption] using t
  have write := tick (x := x) (p := p) (s := s) (h := h) (z := k) (j := h.length)
    (q := .appendBit v) (q' := some (.emitBit v)) (ds := 0) (dh := 0) (move := false)
    (out := out) (sw := none) (hw := some v) (emit := some true) (by simpa) (by simp [tr])
    (by simp) (by simp)
  have emit := tick (x := x) (p := p) (s := s) (h := h++[v]) (z := k) (j := h.length)
    (q := .emitBit v) (q' := some .homeGate) (ds := 0) (dh := 0) (move := false)
    (out := out++[true]) (sw := none) (hw := none) (emit := some v) (by simpa) (by rfl)
    (by simp) (by simp)
  simp [appendOption, List.append_assoc] at write emit
  have back := rewind (h := h++[v]) (q := .homeGate) (r := .first)
    (by intros; rfl) (by intros; rfl) h.length x p s k (s.drop k) (out++[true,v]) hp hk (by simp)
  rw [show 2*h.length+3 = (h.length+2)+(h.length+1) by omega, Nat.add_comm]
  unfold MultiTapeTM.runFrom at *
  have firstTwo : tm.step^[h.length+2] (snap x p s h k 0 (some (.appendBit v)) out) =
      snap x p s (h++[v]) k h.length (some .homeGate) (out++[true,v]) := by
    rw [Function.iterate_succ_apply' tm.step (h.length+1), Function.iterate_succ_apply' tm.step h.length,
      walkFront _ le_rfl, write, emit]
  rw [Function.iterate_add_apply, firstTwo]
  simpa using back

theorem solution (x s h out : List Bool) (p k a b : ℕ) (tail : List Bool)
    (hp : p ≤ x.length) (hk : k ≤ s.length)
    (hs : s.drop k = MultiTapeTM.frame (encGate (a,b)) ++ tail) :
    let q := k + (MultiTapeTM.frame (encGate (a,b))).length
    let v := !(h.getD a true && h.getD b true)
    tm.runFrom (snap x p s h k 0 (some .first) out) (5*a+3*b+2*h.length+8) =
      snap x p s (h++[v]) q 0 (some .first) (out++[true,v]) := by
  dsimp only
  have l := look h a b x p s k tail out hp hk hs
  have len := congrArg List.length hs
  simp only [List.length_drop, List.length_append] at len
  have c := commit h (!(h.getD a true && h.getD b true)) x p s out
    (k+(MultiTapeTM.frame (encGate (a,b))).length) hp (by omega)
  rw [show 5*a+3*b+2*h.length+8 = (2*h.length+3)+(5*a+3*b+5) by omega]
  unfold MultiTapeTM.runFrom at *
  rw [Function.iterate_add_apply, l, c]
