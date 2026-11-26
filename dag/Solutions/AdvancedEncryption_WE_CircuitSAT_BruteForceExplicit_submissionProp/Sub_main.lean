import Definitions.Def_WE_CircuitSAT_Impl_BruteForceExplicit
import SigabaNeoStd.Machines.Gates

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Wire registers and one-hot markers

The wires `v` of the evaluator are kept in a register of fixed width `W`, the wire `i` at
position `W - 1 - i` (`encW`); the index marker after `d` unary digits is the one-hot word
`hot W d` (all `false` once `d ≥ W`). Looking a wire up, writing the next gate's value and
shifting the marker are single `carry` primitives.
-/


namespace SigabaNeo.Tape.BF

open Prog


/-- The wire register. -/
def encW (W : ℕ) (v : List Bool) : List Bool := List.ofFn fun pos : Fin W => v.getD (W - 1 - pos) true

/-- The one-hot marker of the wire `d` (position `W - 1 - d`). -/
def hot (W d : ℕ) : List Bool := List.ofFn fun pos : Fin W => decide (pos.val + d = W - 1)

@[simp] theorem length_encW (W : ℕ) (v : List Bool) : (encW W v).length = W := by simp [encW]
@[simp] theorem length_hot (W d : ℕ) : (hot W d).length = W := by simp [hot]

/-! ### Digit operations without carry -/

theorem carryOp_getElem_of_snd (f : DigitOp) (g : Bool → Bool → Bool)
    (hf : ∀ x y c, (f x y c).1 = g x y) :
    ∀ (xs ys : List Bool) (i : ℕ) (hi : i < (carryOp f xs ys).2.length),
      (carryOp f xs ys).2[i] = g (xs[i]'(by simpa using hi)) (ys.getD i false)
  | [], ys, i, hi => by simp at hi
  | x :: xs, ys, 0, hi => by
    simp only [carryOp, List.getElem_cons_zero, hf, List.getD_eq_getElem?_getD]
    cases ys <;> simp
  | x :: xs, ys, i + 1, hi => by
    simp only [carryOp, List.getElem_cons_succ]
    rw [carryOp_getElem_of_snd f g hf xs ys.tail i]
    cases ys <;> simp

/-! ### Lookup -/

theorem carryOp_lkOp_fst : ∀ (xs ys : List Bool),
    (carryOp lkOp xs ys).1 = true ↔
      ∃ (i : ℕ) (hi : i < xs.length), xs[i] = true ∧ ys.getD i false = false
  | [], ys => by simp
  | x :: xs, ys => by
    have ih := carryOp_lkOp_fst xs ys.tail
    simp only [carryOp, lkOp, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    rw [ih]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨i + 1, by simp; omega, by simpa using h1, ?_⟩
        cases ys <;> simp_all
      · refine ⟨0, by simp, by simpa using h1, ?_⟩
        cases ys <;> simp_all
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero => right; cases ys <;> simp_all
      | succ i =>
        left
        refine ⟨i, by simp at hi; omega, by simpa using h1, ?_⟩
        cases ys <;> simp_all

theorem hd_carryOp_lkOp (x : Bool) (xs ys : List Bool) :
    hd (carryOp lkOp (x :: xs) ys).2 = (carryOp lkOp (x :: xs) ys).1 := by
  simp [carryOp, lkOp, hd]

/-- **Lookup.** The first digit is set iff the wire `d` is `false` (`getD … true`). -/
theorem hd_lookup (W d : ℕ) (v : List Bool) (hW : 0 < W) :
    hd (carryOp lkOp (hot W d) (encW W v)).2 = !(if d < W then v.getD d true else true) := by
  have hne : hot W d ≠ [] := by
    rw [← List.length_pos_iff, length_hot]; exact hW
  obtain ⟨x, xs, hcons⟩ := List.exists_cons_of_ne_nil hne
  rw [hcons, hd_carryOp_lkOp, ← hcons]
  cases hb : (carryOp lkOp (hot W d) (encW W v)).1
  · symm
    rw [Bool.not_eq_false']
    by_contra hne
    split_ifs at hne with hd
    · have hne' : v.getD d true = false := by simpa using hne
      have := (carryOp_lkOp_fst (hot W d) (encW W v)).mpr
        ⟨W - 1 - d, by simp; omega, by simp only [hot, List.getElem_ofFn]; simp; omega, by
          rw [List.getD_eq_getElem _ _ (by simp; omega)]
          simp only [encW, List.getElem_ofFn]
          rw [show W - 1 - (W - 1 - d) = d by omega]
          exact hne'⟩
      rw [hb] at this; exact Bool.noConfusion this
    · exact hne rfl
  · obtain ⟨i, hi, h1, h2⟩ := (carryOp_lkOp_fst _ _).mp hb
    simp only [hot, List.getElem_ofFn, decide_eq_true_eq] at h1
    simp only [length_hot] at hi
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at h2
    simp only [encW, List.getElem_ofFn] at h2
    rw [show W - 1 - i = d by omega] at h2
    rw [if_pos (by omega), h2]; rfl

/-! ### Writing and shifting -/

/-- **Writing** the next wire at the marker of position `|v|`. -/
theorem write_encW (W : ℕ) (v : List Bool) (b : Bool) :
    (carryOp (wrOp b) (encW W v) (hot W v.length)).2 = encW W (v ++ [b]) := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  rw [carryOp_getElem_of_snd (wrOp b) (fun x y => if y then b else x) (fun _ _ _ => rfl)]
  simp only [length_encW, length_carryOp] at h1 h2
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp only [encW, hot, List.getElem_ofFn]
  by_cases hp : i + v.length = W - 1
  · simp only [hp, decide_true, ite_true]
    rw [show W - 1 - i = v.length by omega]
    simp
  · simp only [hp, decide_false]
    simp only [Bool.false_eq_true, ite_false]
    rcases Nat.lt_or_gt_of_ne (show W - 1 - i ≠ v.length by omega) with hl | hl
    · rw [List.getD_append _ _ _ _ hl]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-- **Shifting** the marker to the next wire. -/
theorem shift_hot (W d : ℕ) : (hot W d ++ [false]).tail = hot W (d + 1) := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp only [length_hot] at h2
  rw [List.getElem_tail]
  by_cases hi : i + 1 < W
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [hot, List.getElem_ofFn, decide_eq_decide]
    omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [hot, List.getElem_ofFn, List.getElem_singleton, Bool.false_eq]
    simp only [decide_eq_false_iff_not]
    omega

/-! ### The initial register -/

/-- The assignment of a counter word: input `i` is the bit `X[n - 1 - i]`. -/
def xOf (n : ℕ) (X : List Bool) (i : Fin n) : Bool := X.getD (n - 1 - i) false

/-- **The initial register**: the constant wire, the inputs of the assignment of `X`, and `true`
for every gate. -/
theorem init_encW (W n : ℕ) (X : List Bool) (hX : X.length = n) (hW : n + 1 ≤ W) :
    ((List.replicate W true ++ X).drop X.length ++ [true]).tail =
      encW W (true :: List.ofFn (xOf n X)) := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp only [length_encW] at h2
  rw [List.getElem_tail]
  simp only [encW, List.getElem_ofFn]
  by_cases hi : i + 1 < W
  · rw [List.getElem_append_left (by simp; omega), List.getElem_drop]
    by_cases hj : X.length + (i + 1) < W
    · rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
      rw [List.getD_eq_default _ _ (by simp; omega)]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have e : W - 1 - i = (W - 2 - i) + 1 := by omega
      simp only [e, List.getElem_cons_succ, List.getElem_ofFn, xOf]
      rw [List.getD_eq_getElem _ _ (by omega)]
      congr 1; omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_singleton]
    rw [show W - 1 - i = 0 by omega]
    simp

end SigabaNeo.Tape.BF

/-!
# The streaming evaluator of `evalGates`: abstract automaton

`step1` reads the input tuple `encodeTuple [pw, encGates gs, [β]]` bit by bit (three levels of
frames: the tuple, the gate list, the inner frame of the first index of a gate) and evaluates the
gates on the wires `wires`, a wire `d` (the unary index read so far) being looked up as
`wires.getD d true`.
-/


namespace SigabaNeo.Tape.BF

open Turing.MultiTapeTM

/-- The width of the wire register: `1 + 128` inputs and `2^12` gates. -/
abbrev W : ℕ := 4225

/-- Looking a wire up in the register: wires beyond the register read `true`. -/
def lkW (v : List Bool) (d : ℕ) : Bool := if d < W then v.getD d true else true

/-- The state of the streaming evaluator. -/
structure St where
  m1 : Bool
  v1 : Bool
  v2 : Bool
  m2 : Bool
  m3 : Bool
  ph : Bool
  va : Bool
  last : Bool
  beta : Bool
  d : ℕ
  wires : List Bool

/-- A bit of the gate word `frame (1^a) ++ 1^b`. -/
def step3 (σ : St) (b : Bool) : St :=
  if σ.ph then { σ with d := σ.d + 1 }
  else if σ.m3 then { σ with m3 := false, d := σ.d + 1 }
  else if b then { σ with m3 := true }
  else { σ with va := lkW σ.wires σ.d, d := 0, ph := true }

/-- The value of the gate at the end of its word. -/
def gateVal (σ : St) : Bool := !(σ.va && lkW σ.wires σ.d)

/-- End of a gate. -/
def end2 (σ : St) : St :=
  { σ with wires := σ.wires ++ [gateVal σ], last := gateVal σ, d := 0, ph := false, m3 := false }

/-- A bit of the gate list. -/
def step2 (σ : St) (b : Bool) : St :=
  if σ.m2 then step3 { σ with m2 := false } b
  else if b then { σ with m2 := true }
  else end2 σ

/-- End of a variable of the tuple. -/
def end1 (σ : St) : St :=
  if σ.v2 then σ else if σ.v1 then { σ with v1 := false, v2 := true } else { σ with v1 := true }

/-- A data bit of the tuple. -/
def data1 (σ : St) (b : Bool) : St :=
  if σ.v2 then { σ with beta := b } else if σ.v1 then step2 σ b else σ

/-- A bit of the input. -/
def step1 (σ : St) (b : Bool) : St :=
  if σ.m1 then data1 { σ with m1 := false } b
  else if b then { σ with m1 := true }
  else end1 σ

/-! ### Level 1: frames of the tuple -/

theorem foldl_step1_frame (w : List Bool) (σ : St) (h : σ.m1 = false) :
    (frame w).foldl step1 σ = end1 (w.foldl data1 σ) ∧
      (w.foldl data1 σ).m1 = false := by
  induction w generalizing σ with
  | nil => simp [frame, step1, h]
  | cons b w ih =>
    rw [frame_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons]
    have e : step1 (step1 σ true) b = data1 σ b := by
      simp [step1, h]
      cases σ; simp_all
    rw [e]
    apply ih
    unfold data1 step2 step3 end2
    split_ifs <;> simp_all

theorem foldl_data1_v0 (w : List Bool) (σ : St) (h1 : σ.v1 = false) (h2 : σ.v2 = false) :
    w.foldl data1 σ = σ := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.foldl_cons, show data1 σ b = σ by simp [data1, h1, h2], ih]

theorem foldl_data1_v1 (w : List Bool) (σ : St) (h1 : σ.v1 = true) (h2 : σ.v2 = false) :
    w.foldl data1 σ = w.foldl step2 σ ∧ (w.foldl step2 σ).v1 = true ∧
      (w.foldl step2 σ).v2 = false := by
  induction w generalizing σ with
  | nil => exact ⟨rfl, h1, h2⟩
  | cons b w ih =>
    rw [List.foldl_cons, List.foldl_cons, show data1 σ b = step2 σ b by simp [data1, h1, h2]]
    apply ih
    · unfold step2 step3 end2; split_ifs <;> simp [h1]
    · unfold step2 step3 end2; split_ifs <;> simp [h2]

/-! ### Level 3: the word of a gate -/

theorem foldl_step3_ones (n : ℕ) (σ : St) (h : σ.ph = true) :
    (List.replicate n true).foldl step3 σ = { σ with d := σ.d + n } := by
  induction n generalizing σ with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, show step3 σ true = { σ with d := σ.d + 1 } by
      simp [step3, h], ih { σ with d := σ.d + 1 } h]
    simp only [Nat.add_assoc, Nat.add_comm 1 n]

theorem foldl_step3_frameA (n : ℕ) (σ : St) (h : σ.ph = false) (h3 : σ.m3 = false) :
    (frame (List.replicate n true)).foldl step3 σ =
      { σ with va := lkW σ.wires (σ.d + n), d := 0, ph := true } := by
  induction n generalizing σ with
  | zero => simp [frame, step3, h, h3]
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, List.foldl_cons, List.foldl_cons]
    have e : step3 (step3 σ true) true = { σ with d := σ.d + 1 } := by
      simp [step3, h, h3]
    rw [e, ih { σ with d := σ.d + 1 } h h3]
    simp only [Nat.add_assoc, Nat.add_comm 1 n]

/-- The word of one gate, at level 3, from the start of a gate. -/
theorem foldl_step3_gate (g : ℕ × ℕ) (σ : St) (h : σ.ph = false) (h3 : σ.m3 = false)
    (hd : σ.d = 0) :
    (encGate g).foldl step3 σ =
      { σ with va := lkW σ.wires g.1, d := g.2, ph := true } := by
  rw [encGate, encPair_apply, List.foldl_append, encUnary_apply, encUnary_apply,
    foldl_step3_frameA _ _ h h3, foldl_step3_ones _ _ rfl]
  simp [hd]

/-! ### Level 2: the gate list -/

theorem foldl_step2_frame (u : List Bool) (σ : St) (h : σ.m2 = false) :
    (frame u).foldl step2 σ = end2 (u.foldl step3 σ) ∧ (u.foldl step3 σ).m2 = false := by
  induction u generalizing σ with
  | nil => simp [frame, step2, h]
  | cons b u ih =>
    rw [frame_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons]
    have e : step2 (step2 σ true) b = step3 σ b := by
      simp [step2, h]
      cases σ; simp_all
    rw [e]
    apply ih
    unfold step3; split_ifs <;> simp [h]

/-- The abstract state at the start of a gate. -/
def Ready (σ : St) : Prop := σ.m2 = false ∧ σ.m3 = false ∧ σ.ph = false ∧ σ.d = 0

theorem foldl_step2_gates (gs : GateList) (hg : ∀ g ∈ gs, g.1 < W ∧ g.2 < W) (σ : St)
    (hr : Ready σ) :
    ∃ va, (encGates gs).foldl step2 σ =
      { σ with wires := (gs.foldl estep (σ.wires, σ.last)).1,
               last := (gs.foldl estep (σ.wires, σ.last)).2, va := va } := by
  induction gs generalizing σ with
  | nil => exact ⟨σ.va, by simp⟩
  | cons g gs ih =>
    obtain ⟨h2, h3, hp, hd⟩ := hr
    rw [encGates, encList_cons, List.foldl_append]
    have hf := foldl_step2_frame (encGate g) σ h2
    rw [hf.1, foldl_step3_gate g σ hp h3 hd]
    set σ' := end2 { σ with va := lkW σ.wires g.1, d := g.2, ph := true } with hσ'
    have hr' : Ready σ' := by
      simp [σ', end2, Ready, h2]
    obtain ⟨va, hva⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) σ' hr'
    have hg1 := hg g (by simp)
    refine ⟨va, ?_⟩
    rw [show encList encGate gs = encGates gs from rfl, hva]
    simp [σ', end2, gateVal, List.foldl_cons, estep, h3, hp, hd, lkW, hg1.1, hg1.2]

/-! ### The whole input -/

/-- The initial abstract state. -/
def Init (σ : St) : Prop :=
  σ.m1 = false ∧ σ.v1 = false ∧ σ.v2 = false ∧ σ.m2 = false ∧ σ.m3 = false ∧ σ.ph = false ∧ σ.d = 0

theorem encodeTuple_three (a b c : List Bool) :
    SigabaNeo.encodeTuple [a, b, c] = frame a ++ frame b ++ frame c := by
  simp [SigabaNeo.encodeTuple, encList, encBits]

/-- **The streaming evaluator on an input tuple** computes `evalGates`'s fold and reads `β`. -/
theorem foldl_step1_input (pw : List Bool) (gs : GateList) (hg : ∀ g ∈ gs, g.1 < W ∧ g.2 < W)
    (β : Bool) (σ : St) (h : Init σ) :
    ((SigabaNeo.encodeTuple [pw, encGates gs, [β]]).foldl step1 σ).last =
        (gs.foldl estep (σ.wires, σ.last)).2 ∧
      ((SigabaNeo.encodeTuple [pw, encGates gs, [β]]).foldl step1 σ).beta = β := by
  obtain ⟨h1, hv1, hv2, h2, h3, hp, hd⟩ := h
  rw [encodeTuple_three, List.foldl_append, List.foldl_append]
  have A := foldl_step1_frame pw σ h1
  rw [foldl_data1_v0 pw σ hv1 hv2] at A
  rw [A.1]
  set σ1 := end1 σ with hσ1
  have hσ1' : σ1 = { σ with v1 := true } := by simp [σ1, end1, hv1, hv2]
  have B := foldl_step1_frame (encGates gs) σ1 (by rw [hσ1']; exact h1)
  have C := foldl_data1_v1 (encGates gs) σ1 (by rw [hσ1']) (by rw [hσ1']; exact hv2)
  obtain ⟨va, hva⟩ := foldl_step2_gates gs hg σ1 (by rw [hσ1']; exact ⟨h2, h3, hp, hd⟩)
  rw [B.1, C.1]
  have B2 := B.2
  rw [C.1] at B2
  set σ2 := end1 ((encGates gs).foldl step2 σ1) with hσ2
  have hσ2' : σ2 = { (encGates gs).foldl step2 σ1 with v1 := false, v2 := true } := by
    simp [σ2, end1, C.2.1, C.2.2]
  have D := foldl_step1_frame [β] σ2 (by rw [hσ2']; exact B2)
  rw [D.1]
  have hv2' : σ2.v2 = true := by rw [hσ2']
  have e : [β].foldl data1 σ2 = { σ2 with beta := β } := by simp [data1, hv2']
  rw [e]
  have ee : end1 { σ2 with beta := β } = { σ2 with beta := β } := by simp [end1, hv2']
  rw [ee]
  refine ⟨?_, rfl⟩
  have : σ2.last = (gs.foldl estep (σ.wires, σ.last)).2 := by
    rw [hσ2']; simp only; rw [hva, hσ1']
  exact this

end SigabaNeo.Tape.BF

/-!
# The stream loop on tapes
-/



namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

/-- The store representing the abstract state `σ`, the rest `D` of the input, the popped bit `B`
and the lookup scratch `R`, over the base store `s0`. -/
def SS (s0 : Store K) (σ : St) (D B R P : List Bool) : Store K := fun t =>
  if t = tG then encW W σ.wires else
  if t = tA then hot W σ.d else
  if t = tP then P else
  if t = tD then D else
  if t = tB then B else
  if t = tR then R else
  if t = fm1 then [σ.m1] else
  if t = fv1 then [σ.v1] else
  if t = fv2 then [σ.v2] else
  if t = fm2 then [σ.m2] else
  if t = fm3 then [σ.m3] else
  if t = fph then [σ.ph] else
  if t = fva then [σ.va] else
  if t = flast then [σ.last] else
  if t = fbeta then [σ.beta] else s0 t

/-- The base store: the constant tapes the stream reads. -/
structure Base (s0 : Store K) : Prop where
  tt : s0 tTt = [true]
  tf : s0 tTf = [false]
  ta : s0 tTA = hot W 0

variable {s0 : Store K} {σ : St} {D B R P : List Bool}

section
variable (s0 σ D B R P)

@[simp] theorem SS_tTt : SS s0 σ D B R P tTt = s0 tTt := by simp +decide [SS]
@[simp] theorem SS_tTf : SS s0 σ D B R P tTf = s0 tTf := by simp +decide [SS]
@[simp] theorem SS_tTA : SS s0 σ D B R P tTA = s0 tTA := by simp +decide [SS]
@[simp] theorem SS_tG : SS s0 σ D B R P tG = encW W σ.wires := by simp +decide [SS]
@[simp] theorem SS_tA : SS s0 σ D B R P tA = hot W σ.d := by simp +decide [SS]
@[simp] theorem SS_tP : SS s0 σ D B R P tP = P := by simp +decide [SS]
@[simp] theorem SS_tD : SS s0 σ D B R P tD = D := by simp +decide [SS]
@[simp] theorem SS_tB : SS s0 σ D B R P tB = B := by simp +decide [SS]
@[simp] theorem SS_tR : SS s0 σ D B R P tR = R := by simp +decide [SS]
@[simp] theorem SS_fm1 : SS s0 σ D B R P fm1 = [σ.m1] := by simp +decide [SS]
@[simp] theorem SS_fv1 : SS s0 σ D B R P fv1 = [σ.v1] := by simp +decide [SS]
@[simp] theorem SS_fv2 : SS s0 σ D B R P fv2 = [σ.v2] := by simp +decide [SS]
@[simp] theorem SS_fm2 : SS s0 σ D B R P fm2 = [σ.m2] := by simp +decide [SS]
@[simp] theorem SS_fm3 : SS s0 σ D B R P fm3 = [σ.m3] := by simp +decide [SS]
@[simp] theorem SS_fph : SS s0 σ D B R P fph = [σ.ph] := by simp +decide [SS]
@[simp] theorem SS_fva : SS s0 σ D B R P fva = [σ.va] := by simp +decide [SS]
@[simp] theorem SS_flast : SS s0 σ D B R P flast = [σ.last] := by simp +decide [SS]
@[simp] theorem SS_fbeta : SS s0 σ D B R P fbeta = [σ.beta] := by simp +decide [SS]

/-! ### Updates of the represented tapes -/

theorem upd_tG (v : List Bool) :
    Function.update (SS s0 σ D B R P) tG (encW W v) = SS s0 { σ with wires := v } D B R P := by
  funext t; by_cases h : t = tG <;> simp +decide [SS, h]

theorem upd_tP (P' : List Bool) :
    Function.update (SS s0 σ D B R P) tP P' = SS s0 σ D B R P' := by
  funext t; by_cases h : t = tP <;> simp +decide [SS, h]

theorem upd_tA (d : ℕ) :
    Function.update (SS s0 σ D B R P) tA (hot W d) = SS s0 { σ with d := d } D B R P := by
  funext t; by_cases h : t = tA <;> simp +decide [SS, h]

theorem upd_tD (D' : List Bool) :
    Function.update (SS s0 σ D B R P) tD D' = SS s0 σ D' B R P := by
  funext t; by_cases h : t = tD <;> simp +decide [SS, h]

theorem upd_tB (B' : List Bool) :
    Function.update (SS s0 σ D B R P) tB B' = SS s0 σ D B' R P := by
  funext t; by_cases h : t = tB <;> simp +decide [SS, h]

theorem upd_tR (R' : List Bool) :
    Function.update (SS s0 σ D B R P) tR R' = SS s0 σ D B R' P := by
  funext t; by_cases h : t = tR <;> simp +decide [SS, h]

theorem upd_fm1 (b : Bool) : Function.update (SS s0 σ D B R P) fm1 [b] = SS s0 { σ with m1 := b } D B R P := by
  funext t; by_cases h : t = fm1 <;> simp +decide [SS, h]
theorem upd_fv1 (b : Bool) : Function.update (SS s0 σ D B R P) fv1 [b] = SS s0 { σ with v1 := b } D B R P := by
  funext t; by_cases h : t = fv1 <;> simp +decide [SS, h]
theorem upd_fv2 (b : Bool) : Function.update (SS s0 σ D B R P) fv2 [b] = SS s0 { σ with v2 := b } D B R P := by
  funext t; by_cases h : t = fv2 <;> simp +decide [SS, h]
theorem upd_fm2 (b : Bool) : Function.update (SS s0 σ D B R P) fm2 [b] = SS s0 { σ with m2 := b } D B R P := by
  funext t; by_cases h : t = fm2 <;> simp +decide [SS, h]
theorem upd_fm3 (b : Bool) : Function.update (SS s0 σ D B R P) fm3 [b] = SS s0 { σ with m3 := b } D B R P := by
  funext t; by_cases h : t = fm3 <;> simp +decide [SS, h]
theorem upd_fph (b : Bool) : Function.update (SS s0 σ D B R P) fph [b] = SS s0 { σ with ph := b } D B R P := by
  funext t; by_cases h : t = fph <;> simp +decide [SS, h]
theorem upd_fva (b : Bool) : Function.update (SS s0 σ D B R P) fva [b] = SS s0 { σ with va := b } D B R P := by
  funext t; by_cases h : t = fva <;> simp +decide [SS, h]
theorem upd_flast (b : Bool) : Function.update (SS s0 σ D B R P) flast [b] = SS s0 { σ with last := b } D B R P := by
  funext t; by_cases h : t = flast <;> simp +decide [SS, h]
theorem upd_fbeta (b : Bool) : Function.update (SS s0 σ D B R P) fbeta [b] = SS s0 { σ with beta := b } D B R P := by
  funext t; by_cases h : t = fbeta <;> simp +decide [SS, h]

end

/-! ### The fragments of the stream body -/

attribute [local simp] upd_tG upd_tP upd_tA upd_tD upd_tB upd_tR upd_fm1 upd_fv1 upd_fv2 upd_fm2
  upd_fm3 upd_fph upd_fva upd_flast upd_fbeta

/-- The lookup word. -/
def lkWord (σ : St) : List Bool := (carryOp lkOp (hot W σ.d) (encW W σ.wires)).2

theorem hd_lkWord (σ : St) : hd (lkWord σ) = !(lkW σ.wires σ.d) := by
  rw [lkWord, hd_lookup W σ.d σ.wires (by norm_num), lkW]

theorem run_look : run look (SS s0 σ D B R P) = SS s0 σ D B (lkWord σ) P := by
  simp [look, lkWord, run_prim, Prim.apply]

theorem run_setT (hb : Base s0) (f : Fin K) :
    run (setT f) (SS s0 σ D B R P) = Function.update (SS s0 σ D B R P) f [true] := by
  simp [setT, hb.tt]

theorem run_setF (hb : Base s0) (f : Fin K) :
    run (setF f) (SS s0 σ D B R P) = Function.update (SS s0 σ D B R P) f [false] := by
  simp [setF, hb.tf]

attribute [local simp] run_setT run_setF

theorem run_shiftA : run shiftA (SS s0 σ D B R P) = SS s0 { σ with d := σ.d + 1 } D B R P := by
  simp [shiftA, shift_hot]

theorem run_resetA (hb : Base s0) :
    run (cp tA tTA) (SS s0 σ D B R P) = SS s0 { σ with d := 0 } D B R P := by
  simp [hb.ta]

theorem run_pEnd3 (hb : Base s0) :
    run pEnd3 (SS s0 σ D B R P) =
      SS s0 { σ with va := lkW σ.wires σ.d, d := 0, ph := true } D B (lkWord σ) P := by
  simp only [pEnd3, run_seq, run_look, run_ifBit, SS_tR, hd_lkWord]
  cases h : lkW σ.wires σ.d <;> simp [hb, hb.ta, hb.tt, hb.tf]

@[simp] theorem hd_singleton (b : Bool) : hd [b] = b := rfl

theorem run_pStep3 (hb : Base s0) : ∃ R', run pStep3 (SS s0 σ D B R P) =
    SS s0 (step3 σ (hd B)) D B R' P := by
  simp only [pStep3, run_ifBit, SS_fph, SS_fm3, SS_tB, hd_singleton]
  rcases σ with ⟨m1, v1, v2, m2, m3, ph, va, last, beta, d, wires⟩
  cases ph
  · cases m3
    · cases hB : hd B
      · exact ⟨lkWord ⟨m1, v1, v2, m2, false, false, va, last, beta, d, wires⟩,
          by simp [run_pEnd3 hb, step3, hB]⟩
      · exact ⟨R, by simp [hb, step3, hB]⟩
    · exact ⟨R, by simp [hb, step3, run_shiftA]⟩
  · exact ⟨R, by simp [step3, run_shiftA]⟩

theorem run_wr (hb : Base s0) (b : Bool) :
    run (wr b) (SS s0 σ D B R (hot W σ.wires.length)) =
      SS s0 { σ with wires := σ.wires ++ [b], last := b } D B R (hot W σ.wires.length) := by
  cases b <;> simp [wr, hb, run_prim, Prim.apply, write_encW]

theorem run_pEnd2 (hb : Base s0) :
    run pEnd2 (SS s0 σ D B R (hot W σ.wires.length)) =
      SS s0 (end2 σ) D B (lkWord σ) (hot W (end2 σ).wires.length) := by
  simp only [pEnd2, run_seq, run_look, run_ifBit, SS_fva, SS_tR, hd_lkWord, hd_singleton]
  have e : ∀ b : Bool, run (sin false tP ⨾ cp tA tTA ⨾ setF fph ⨾ setF fm3)
      (SS s0 { σ with wires := σ.wires ++ [b], last := b } D B (lkWord σ) (hot W σ.wires.length)) =
      SS s0 { σ with wires := σ.wires ++ [b], last := b, d := 0, ph := false, m3 := false } D B
        (lkWord σ) (hot W (σ.wires.length + 1)) := by
    intro b
    simp [hb, hb.ta, shift_hot]
  rcases σ with ⟨m1, v1, v2, m2, m3, ph, va, last, beta, d, wires⟩
  cases va <;> cases h : lkW wires d <;>
    simp [run_wr hb, end2, gateVal, h, hb, hb.ta, shift_hot]

theorem wires_step3 (σ : St) (b : Bool) : (step3 σ b).wires = σ.wires := by
  unfold step3; split_ifs <;> rfl

theorem run_pStep2 (hb : Base s0) : ∃ R', run pStep2 (SS s0 σ D B R (hot W σ.wires.length)) =
    SS s0 (step2 σ (hd B)) D B R' (hot W (step2 σ (hd B)).wires.length) := by
  simp only [pStep2, run_ifBit, SS_fm2, SS_tB, hd_singleton]
  rcases σ with ⟨m1, v1, v2, m2, m3, ph, va, last, beta, d, wires⟩
  cases m2
  · cases hB : hd B
    · exact ⟨lkWord ⟨m1, v1, v2, false, m3, ph, va, last, beta, d, wires⟩,
        by simp [run_pEnd2 hb, step2, hB]⟩
    · exact ⟨R, by simp [hb, step2, hB]⟩
  · simp only [ite_true, run_seq, run_setF hb, upd_fm2]
    obtain ⟨R', h⟩ := run_pStep3 (s0 := s0) (σ := ⟨m1, v1, v2, false, m3, ph, va, last, beta, d, wires⟩)
      (D := D) (B := B) (R := R) (P := hot W wires.length) hb
    exact ⟨R', by rw [h]; simp [step2, wires_step3]⟩

theorem run_pEnd1 (hb : Base s0) :
    run pEnd1 (SS s0 σ D B R P) = SS s0 (end1 σ) D B R P := by
  rcases σ with ⟨m1, v1, v2, m2, m3, ph, va, last, beta, d, wires⟩
  cases v1 <;> cases v2 <;> simp [pEnd1, run_ifBit, hb, end1]

theorem hd_take_one (D : List Bool) : hd (D.take 1) = hd D := by cases D <;> rfl

/-- **The body of the stream loop** runs one step of the automaton on the next input bit. -/
theorem run_pStep1 (hb : Base s0) :
    run pStep1 (SS s0 σ D [] [] (hot W σ.wires.length)) =
      SS s0 (step1 σ (hd D)) D.tail [] [] (hot W (step1 σ (hd D)).wires.length) := by
  have hpop : run (pp tD tB) (SS s0 σ D [] [] (hot W σ.wires.length)) =
      SS s0 σ D.tail (D.take 1) [] (hot W σ.wires.length) := by
    simp [pp]
  have hclr : ∀ τ B R P, run (clr tB ⨾ clr tR) (SS s0 τ D.tail B R P) =
      SS s0 τ D.tail [] [] P := by
    intro τ B R P; simp [clr]
  simp only [pStep1, run_seq] at hclr ⊢
  rw [hpop]
  simp only [run_ifBit, SS_fm1, SS_fv1, SS_fv2, SS_tB, hd_singleton, hd_take_one]
  rcases σ with ⟨m1, v1, v2, m2, m3, ph, va, last, beta, d, wires⟩
  cases m1
  · cases hD : hd D
    · simp only [Bool.false_eq_true, ite_false]
      rw [run_pEnd1 hb, hclr]; simp [step1, hD]; rcases v1 <;> rcases v2 <;> rfl
    · simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [run_setT hb, upd_fm1, hclr]; simp [step1, hD]
  · simp only [ite_true, run_seq, run_setF hb, upd_fm1, SS_fv1, SS_fv2, SS_tB, hd_take_one]
    cases v2
    · cases v1
      · simp only [Bool.false_eq_true, ite_false, run_nop, run_ifBit, SS_fv1, SS_fv2, hd_singleton]
        rw [hclr]; simp [step1, data1]
      · simp only [ite_true, Bool.false_eq_true, ite_false, run_ifBit, SS_fv1, SS_fv2, hd_singleton]
        obtain ⟨R', h⟩ := run_pStep2 (s0 := s0)
          (σ := ⟨false, true, false, m2, m3, ph, va, last, beta, d, wires⟩)
          (D := D.tail) (B := D.take 1) (R := []) hb
        rw [h, hd_take_one, hclr]; simp [step1, data1]
    · cases hD : hd D <;> simp [hb, hclr, step1, data1, hD, run_ifBit]

end SigabaNeo.Tape.BF

/-!
# One evaluation of the circuit
-/



namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

theorem SS_update_tK (s0 : Store K) (σ : St) (D B R P w : List Bool) :
    Function.update (SS s0 σ D B R P) tK w = SS (Function.update s0 tK w) σ D B R P := by
  funext t; by_cases h : t = tK <;> simp +decide [SS, h]

theorem Base.update_tK {s0 : Store K} (hb : Base s0) (w : List Bool) :
    Base (Function.update s0 tK w) :=
  ⟨by rw [Function.update_of_ne (by decide)]; exact hb.tt,
    by rw [Function.update_of_ne (by decide)]; exact hb.tf,
    by rw [Function.update_of_ne (by decide)]; exact hb.ta⟩

/-- One round of the stream loop on the abstract state and the rest of the input. -/
def sstep (a : St × List Bool) : St × List Bool := (step1 a.1 (hd a.2), a.2.tail)

theorem iterate_sstep : ∀ (D : List Bool) (σ : St), sstep^[D.length] (σ, D) = (D.foldl step1 σ, [])
  | [], σ => rfl
  | b :: D, σ => by
    rw [List.length_cons, Function.iterate_succ_apply]
    exact iterate_sstep D (step1 σ b)

/-- **The stream loop**: the automaton over the whole input `D`. -/
theorem run_stream {s0 : Store K} (hb : Base s0) (σ : St) (D w : List Bool)
    (hw : w.length = D.length) :
    run (loop tK pStep1) (Function.update (SS s0 σ D [] [] (hot W σ.wires.length)) tK w) =
      Function.update (SS s0 (D.foldl step1 σ) [] [] [] (hot W (D.foldl step1 σ).wires.length)) tK [] := by
  have h := run_loop_iter tK pStep1
    (fun a : St × List Bool => SS s0 a.1 a.2 [] [] (hot W a.1.wires.length)) sstep (fun _ => True)
    (fun a w _ => by
      simp only [SS_update_tK]
      exact run_pStep1 (hb.update_tK w))
    (fun _ _ => trivial) w (σ, D) trivial
  simp only at h
  rw [h, hw, iterate_sstep]

/-! ### Initialisation -/

/-- The initial abstract state for the counter word `X`. -/
def σInit (X : List Bool) : St where
  m1 := false
  v1 := false
  v2 := false
  m2 := false
  m3 := false
  ph := false
  va := true
  last := true
  beta := false
  d := 0
  wires := true :: List.ofFn (xOf 128 X)

/-- The fixed tapes the evaluation needs. -/
structure Good (x : List Bool) (s : Store K) : Prop where
  tI : s tI = x
  tt : s tTt = [true]
  tf : s tTf = [false]
  tg : s tTG = List.replicate W true
  ta : s tTA = hot W 0
  tp : s tTP = hot W 129
  xlen : (s tX).length = 128

/-- The base store of the stream after the initialisation. -/
def baseOf (s : Store K) : Store K := Function.update (Function.update s tXC []) tMC []

theorem run_evalInit {x : List Bool} {s : Store K} (hg : Good x s) :
    run evalInit s = Function.update (SS (baseOf s) (σInit (s tX)) x [] [] (hot W 129)) tK x := by
  have hG : ((List.replicate W true ++ s tX).drop (s tX).length ++ [true]).tail =
      encW W (σInit (s tX)).wires := init_encW W 128 (s tX) hg.xlen (by norm_num)
  simp only [evalInit, run_seq, run_copy, run_moveBits tG tXC tMC (by decide) (by decide) (by decide),
    run_sin, setT, setF, run_clear, clr]
  simp +decide only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true]
  rw [hg.tg, hG, hg.tI, hg.tt, hg.tf, hg.ta, hg.tp]
  funext t
  have hl : (σInit (s tX)).wires.length = 129 := by simp [σInit]
  by_cases h0 : t = tG
  · subst h0; simp +decide [SS, baseOf, hl, σInit]
  by_cases h1 : t = tA
  · subst h1; simp +decide [SS, baseOf, hl, σInit]
  by_cases h2 : t = tP
  · subst h2; simp +decide [SS, baseOf, hl, σInit]
  by_cases h3 : t = tD
  · subst h3; simp +decide [SS, baseOf, hl, σInit]
  by_cases h4 : t = tB
  · subst h4; simp +decide [SS, baseOf, hl, σInit]
  by_cases h5 : t = tR
  · subst h5; simp +decide [SS, baseOf, hl, σInit]
  by_cases h6 : t = fm1
  · subst h6; simp +decide [SS, baseOf, hl, σInit]
  by_cases h7 : t = fv1
  · subst h7; simp +decide [SS, baseOf, hl, σInit]
  by_cases h8 : t = fv2
  · subst h8; simp +decide [SS, baseOf, hl, σInit]
  by_cases h9 : t = fm2
  · subst h9; simp +decide [SS, baseOf, hl, σInit]
  by_cases h10 : t = fm3
  · subst h10; simp +decide [SS, baseOf, hl, σInit]
  by_cases h11 : t = fph
  · subst h11; simp +decide [SS, baseOf, hl, σInit]
  by_cases h12 : t = fva
  · subst h12; simp +decide [SS, baseOf, hl, σInit]
  by_cases h13 : t = flast
  · subst h13; simp +decide [SS, baseOf, hl, σInit]
  by_cases h14 : t = fbeta
  · subst h14; simp +decide [SS, baseOf, hl, σInit]
  by_cases h15 : t = tK
  · subst h15; simp +decide [SS, baseOf, hl, σInit]
  by_cases h16 : t = tXC
  · subst h16; simp +decide [SS, baseOf, hl, σInit]
  by_cases h17 : t = tMC
  · subst h17; simp +decide [SS, baseOf, hl, σInit]
  simp [SS, baseOf, Function.update_apply, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem base_baseOf {x : List Bool} {s : Store K} (hg : Good x s) : Base (baseOf s) :=
  ⟨by rw [BF.baseOf, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hg.tt,
    by rw [BF.baseOf, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hg.tf,
    by rw [BF.baseOf, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hg.ta⟩

/-- The final abstract state of the evaluation of the counter word `X` on the input `x`. -/
def σFin (x X : List Bool) : St := x.foldl step1 (σInit X)

/-- The tapes one evaluation writes. -/
def evalTapes : List (Fin K) :=
  [tG, tA, tP, tD, tB, tR, fm1, fv1, fv2, fm2, fm3, fph, fva, flast, fbeta, tK, tXC, tMC, tX, fres]

/-- **One evaluation.** -/
theorem run_evalOne {x : List Bool} {s : Store K} (hg : Good x s) :
    (run evalOne s) tX = (carryOp addBit (s tX) (s tOne)).2 ∧
    (run evalOne s) fres = (if (σFin x (s tX)).last then [true] else s fres) ∧
    (run evalOne s) fbeta = [(σFin x (s tX)).beta] ∧
    ∀ t, t ∉ evalTapes → (run evalOne s) t = s t := by
  have hl : (σInit (s tX)).wires.length = 129 := by simp [σInit]
  have h1 : run (loop tK pStep1) (run evalInit s) =
      Function.update (SS (baseOf s) (σFin x (s tX)) [] [] [] (hot W (σFin x (s tX)).wires.length))
        tK [] := by
    rw [run_evalInit hg, ← hl, run_stream (base_baseOf hg) _ x x rfl]; rfl
  rw [evalOne, run_seq, run_seq, h1]
  simp only [evalFin, run_seq, run_ifBit, setT, run_copy, run_nop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : (σFin x (s tX)).last <;> simp +decide [SS, run_prim, Prim.apply, baseOf, h]
  · cases h : (σFin x (s tX)).last <;> simp +decide [SS, run_prim, Prim.apply, baseOf, h, hg.tt]
  · cases h : (σFin x (s tX)).last <;> simp +decide [SS, run_prim, Prim.apply, baseOf, h]
  · intro t ht
    simp only [evalTapes, List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := ht
    cases h : (σFin x (s tX)).last <;>
      simp +decide [h, SS, run_prim, Prim.apply, baseOf, Function.update_apply, h0, h1, h2, h3, h4, h5, h6, h7, h8,
        h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

end SigabaNeo.Tape.BF

/-!
# Programs that never mention a tape

A program that neither reads nor writes tape `c` commutes with every update of `c`.
-/

namespace SigabaNeo.Tape

namespace Prim

variable {k : ℕ}

/-- The tapes a primitive reads or writes. -/
def bfTapes : Prim k → List (Fin k)
  | clear i | tail i | cons i _ | snoc i _ => [i]
  | copy i j | carry _ i j | pop i j | consHead i j | snocHead i j => [i, j]
  | eq i j f => [i, j, f]

theorem bf_apply_update (p : Prim k) (c : Fin k) (hc : c ∉ p.bfTapes) (s : Store k) (w : List Bool) :
    p.apply (Function.update s c w) = Function.update (p.apply s) c w := by
  funext t
  cases p <;> simp only [bfTapes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc <;>
    simp only [apply, Function.update_apply] <;> split_ifs <;> simp_all

end Prim

namespace Prog

variable {k : ℕ}

/-- `p` never mentions the tape `c`. -/
noncomputable def bfAvoidsB (c : Fin k) : Prog k → Bool
  | prim p => !(p.bfTapes.contains c)
  | coin i => i != c
  | seq p q => p.bfAvoidsB c && q.bfAvoidsB c
  | ifBlank i p q => (i != c) && p.bfAvoidsB c && q.bfAvoidsB c
  | ifBit i p q => (i != c) && p.bfAvoidsB c && q.bfAvoidsB c
  | loop i body => (i != c) && body.bfAvoidsB c

/-- **A program that never mentions `c` commutes with the updates of `c`.** -/
theorem run_update_of_avoids (c : Fin k) :
    ∀ (p : Prog k), p.bfAvoidsB c = true → ∀ (s : Store k) (w : List Bool),
      run p (Function.update s c w) = Function.update (run p s) c w
  | prim p, h, s, w => by
    have h' : c ∉ p.bfTapes := by simpa [bfAvoidsB] using h
    exact Prim.bf_apply_update p c h' s w
  | coin i, h, s, w => by
    simp only [bfAvoidsB, bne_iff_ne, ne_eq] at h
    simp only [run]; rw [Function.update_comm h]
  | seq p q, h, s, w => by
    simp only [bfAvoidsB, Bool.and_eq_true] at h
    simp only [run_seq, run_update_of_avoids c p h.1, run_update_of_avoids c q h.2]
  | ifBlank i p q, h, s, w => by
    simp only [bfAvoidsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [run_ifBlank, Function.update_of_ne h.1.1]
    split_ifs
    · exact run_update_of_avoids c p h.1.2 s w
    · exact run_update_of_avoids c q h.2 s w
  | ifBit i p q, h, s, w => by
    simp only [bfAvoidsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [run_ifBit, Function.update_of_ne h.1.1]
    split_ifs
    · exact run_update_of_avoids c p h.1.2 s w
    · exact run_update_of_avoids c q h.2 s w
  | loop i body, h, s, w => by
    simp only [bfAvoidsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [run_loop, Function.update_of_ne h.1]
    have hf : ∀ t, run body (tailAt i (Function.update t c w)) =
        Function.update (run body (tailAt i t)) c w := by
      intro t
      rw [tailAt, Function.update_of_ne h.1, ← Function.update_comm h.1,
        run_update_of_avoids c body h.2]; rfl
    generalize (s i).length = n
    induction n generalizing s with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hf, ih]

end Prog

end SigabaNeo.Tape

/-!
# The enumeration of all assignments
-/


namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

/-- The word `1` of the counter. -/
def one128 : List Bool := List.replicate 127 false ++ [true]

/-- The increment of the counter word. -/
def incW (X : List Bool) : List Bool := (carryOp addBit X one128).2

/-- `lastOf x X`: the circuit's output on the assignment of `X`. -/
noncomputable def orIter (x : List Bool) : ℕ → List Bool → Bool
  | 0, _ => false
  | n + 1, X => (σFin x X).last || orIter x n (incW X)

theorem orIter_add (x : List Bool) : ∀ (a b : ℕ) (X : List Bool),
    orIter x (a + b) X = (orIter x a X || orIter x b (incW^[a] X))
  | 0, b, X => by simp [orIter]
  | a + 1, b, X => by
    rw [show a + 1 + b = (a + b) + 1 by omega, orIter, orIter, orIter_add x a b,
      Function.iterate_succ_apply, Bool.or_assoc]

/-- The fixed tapes during the enumeration. -/
structure GoodN (x : List Bool) (s : Store K) : Prop where
  good : Good x s
  t16 : s tT16 = List.replicate 65536 true
  one : s tOne = one128
  res : ∃ r, s fres = [r]
  out : s tO = []

theorem goodN_evalOne {x : List Bool} {s : Store K} (h : GoodN x s) :
    GoodN x (run evalOne s) ∧ (run evalOne s) tX = incW (s tX) ∧
      (run evalOne s) fres = [hd (s fres) || (σFin x (s tX)).last] ∧
      (run evalOne s) fbeta = [(σFin x (s tX)).beta] := by
  obtain ⟨hX, hr, hb, ho⟩ := run_evalOne h.good
  have ho' : ∀ t, t ∉ evalTapes → (run evalOne s) t = s t := ho
  have keep : ∀ t, t ∉ evalTapes → (run evalOne s) t = s t := ho
  obtain ⟨r, hr0⟩ := h.res
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, hb⟩
  · rw [keep _ (by decide)]; exact h.good.tI
  · rw [keep _ (by decide)]; exact h.good.tt
  · rw [keep _ (by decide)]; exact h.good.tf
  · rw [keep _ (by decide)]; exact h.good.tg
  · rw [keep _ (by decide)]; exact h.good.ta
  · rw [keep _ (by decide)]; exact h.good.tp
  · rw [hX, length_carryOp]; exact h.good.xlen
  · rw [keep _ (by decide)]; exact h.t16
  · rw [keep _ (by decide)]; exact h.one
  · rw [hr]; split_ifs <;> simp [hr0]
  · rw [keep _ (by decide)]; exact h.out
  · rw [hX, h.one]; rfl
  · rw [hr, hr0]; cases (σFin x (s tX)).last <;> simp [hd]

theorem nest_avoids : ∀ i : Fin 8, (nest i.val).bfAvoidsB (cE i) = true := by decide

theorem nest_succ (m : ℕ) (h : m < 8) :
    nest (m + 1) = cp (cE ⟨m, h⟩) tT16 ⨾ loop (cE ⟨m, h⟩) (nest m) := by
  simp [nest, h]

/-- **The enumeration loops.** -/
theorem run_nest {x : List Bool} {β : Bool} (hβ : ∀ X, (σFin x X).beta = β) :
    ∀ m, m ≤ 8 → ∀ s, GoodN x s →
      GoodN x (run (nest m) s) ∧ (run (nest m) s) tX = incW^[65536 ^ m] (s tX) ∧
      hd ((run (nest m) s) fres) = (hd (s fres) || orIter x (65536 ^ m) (s tX)) ∧
      (run (nest m) s) fbeta = [β]
  | 0, _, s, h => by
    rw [show nest 0 = evalOne from rfl]
    obtain ⟨h1, h2, h3, h4⟩ := goodN_evalOne h
    refine ⟨h1, h2, ?_, by rw [h4, hβ]⟩
    rw [h3]; simp [orIter, hd]
  | m + 1, hm, s, h => by
    have hm' : m < 8 := by omega
    have ih := run_nest hβ m (by omega)
    set c := cE ⟨m, hm'⟩
    set F := run (nest m)
    have it : ∀ j, 1 ≤ j → GoodN x (F^[j] s) ∧ (F^[j] s) tX = incW^[65536 ^ m * j] (s tX) ∧
        hd ((F^[j] s) fres) = (hd (s fres) || orIter x (65536 ^ m * j) (s tX)) ∧
        (F^[j] s) fbeta = [β] := by
      intro j hj
      induction j with
      | zero => omega
      | succ j ihj =>
        rcases Nat.eq_zero_or_pos j with rfl | hj'
        · simpa using ih s h
        obtain ⟨g1, g2, g3, g4⟩ := ihj hj'
        obtain ⟨k1, k2, k3, k4⟩ := ih _ g1
        rw [Function.iterate_succ_apply']
        refine ⟨k1, ?_, ?_, k4⟩
        · rw [k2, g2, ← Function.iterate_add_apply, show 65536 ^ m * (j + 1) = 65536 ^ m + 65536 ^ m * j by ring,
            Nat.add_comm]
        · rw [k3, g3, g2, Bool.or_assoc, ← orIter_add,
            show 65536 ^ m * (j + 1) = 65536 ^ m * j + 65536 ^ m by ring]
    have hl := run_loop_iter c (nest m) id F (fun _ => True)
      (fun a w _ => run_update_of_avoids c (nest m) (nest_avoids ⟨m, hm'⟩) a w)
      (fun _ _ => trivial) (s tT16) s trivial
    simp only [id] at hl
    rw [nest_succ m hm', run_seq, run_copy, hl, h.t16, List.length_replicate]
    obtain ⟨g1, g2, g3, g4⟩ := it 65536 (by norm_num)
    have hc : ∀ t, t ≠ c → Function.update (F^[65536] s) c [] t = (F^[65536] s) t :=
      fun t ht => Function.update_of_ne ht _ _
    have hne : ∀ t : Fin K, t.val < 32 → t ≠ c := by
      intro t ht h; rw [Fin.ext_iff] at h; simp [c, cE] at h; omega
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hc _ (hne _ (by decide))]; exact g1.good.tI
    · rw [hc _ (hne _ (by decide))]; exact g1.good.tt
    · rw [hc _ (hne _ (by decide))]; exact g1.good.tf
    · rw [hc _ (hne _ (by decide))]; exact g1.good.tg
    · rw [hc _ (hne _ (by decide))]; exact g1.good.ta
    · rw [hc _ (hne _ (by decide))]; exact g1.good.tp
    · rw [hc _ (hne _ (by decide))]; exact g1.good.xlen
    · rw [hc _ (hne _ (by decide))]; exact g1.t16
    · rw [hc _ (hne _ (by decide))]; exact g1.one
    · rw [hc _ (hne _ (by decide))]; exact g1.res
    · rw [hc _ (hne _ (by decide))]; exact g1.out
    · rw [hc _ (hne _ (by decide)), g2, pow_succ]
    · rw [hc _ (hne _ (by decide)), g3, pow_succ]
    · rw [hc _ (hne _ (by decide)), g4]

end SigabaNeo.Tape.BF

/-!
# Counting through all words
-/


namespace SigabaNeo.Tape.BF

open Prog

theorem bitsVal_inj : ∀ (a b : List Bool), a.length = b.length → bitsVal a = bitsVal b → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [bitsVal] at hv
    have h1 := bitsVal_lt xs
    have h2 := bitsVal_lt ys
    rw [hl] at h1 hv
    have hxy : x = y := by
      cases x <;> cases y
      · rfl
      · simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add] at hv; omega
      · simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add] at hv; omega
      · rfl
    subst hxy
    have : bitsVal xs = bitsVal ys := by omega
    rw [bitsVal_inj xs ys hl this]

theorem length_one128 : one128.length = 128 := by simp [one128]

theorem bitsVal_one128 : bitsVal one128 = 1 := by
  simp [one128, bitsVal, List.replicate_succ]

theorem length_incW (X : List Bool) : (incW X).length = X.length := by simp [incW]

theorem bitsVal_incW (X : List Bool) (h : X.length = 128) :
    bitsVal (incW X) = (bitsVal X + 1) % 2 ^ 128 := by
  rw [incW, bitsVal_add _ _ (by rw [h, length_one128]), bitsVal_one128, h]

theorem iterate_incW (k : ℕ) : (incW^[k] (List.replicate 128 false)).length = 128 ∧
    bitsVal (incW^[k] (List.replicate 128 false)) = k % 2 ^ 128 := by
  induction k with
  | zero =>
    have h0 : ∀ n, bitsVal (List.replicate n false) = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, bitsVal, ih]
    exact ⟨List.length_replicate, by rw [Function.iterate_zero_apply, h0]; rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply', length_incW, bitsVal_incW _ ih.1, ih.2]
    exact ⟨ih.1, by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]⟩

theorem orIter_iff (x : List Bool) : ∀ (n : ℕ) (X : List Bool),
    orIter x n X = true ↔ ∃ k < n, (σFin x (incW^[k] X)).last = true
  | 0, X => by simp [orIter]
  | n + 1, X => by
    rw [orIter, Bool.or_eq_true, orIter_iff x n]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨k + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero => left; exact h
      | succ k => right; exact ⟨k, by omega, by rwa [Function.iterate_succ_apply] at h⟩

/-- **The enumeration visits every word of 128 bits.** -/
theorem orIter_all (x : List Bool) :
    orIter x (2 ^ 128) (List.replicate 128 false) = true ↔
      ∃ X : List Bool, X.length = 128 ∧ (σFin x X).last = true := by
  rw [orIter_iff]
  constructor
  · rintro ⟨k, _, h⟩; exact ⟨_, (iterate_incW k).1, h⟩
  · rintro ⟨X, hX, h⟩
    refine ⟨bitsVal X, by have := bitsVal_lt X; rwa [hX] at this, ?_⟩
    have e : incW^[bitsVal X] (List.replicate 128 false) = X := by
      apply bitsVal_inj _ _ (by rw [(iterate_incW _).1, hX])
      rw [(iterate_incW _).2, Nat.mod_eq_of_lt (by have := bitsVal_lt X; rwa [hX] at this)]
    rw [e]; exact h

end SigabaNeo.Tape.BF

/-!
# The templates and the output frame
-/


namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog

theorem run_app (T S : Fin K) (b : Bool) (hT : T ≠ tC) (s : Store K) :
    run (app T S b) s =
      Function.update (Function.update s T (s T ++ List.replicate (s S).length b)) tC [] := by
  have h := run_loop_iter tC (prim (.snoc T b)) (fun a => Function.update s T a) (fun a => a ++ [b])
    (fun _ => True) (fun a w _ => by
      rw [run_prim, Prim.apply, Function.update_of_ne hT, Function.update_self,
        Function.update_comm hT, Function.update_idem, Function.update_comm (Ne.symm hT)])
    (fun _ _ => trivial) (s S) (s T) trivial
  have it : ∀ n (a : List Bool), (fun a => a ++ [b])^[n] a = a ++ List.replicate n b := by
    intro n; induction n with
    | zero => simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply', ih, List.replicate_succ', List.append_assoc]
  rw [app, run_seq, run_copy, show Function.update s tC (s S) =
    Function.update (Function.update s T (s T)) tC (s S) by rw [Function.update_eq_self], h, it]

theorem run_dbl (T : Fin K) (b : Bool) (hT : T ≠ tC) (m : ℕ) :
    ∀ (n : ℕ) (s : Store K), s T = List.replicate m b →
      run (dbl T b (n + 1)) s =
        Function.update (Function.update s T (List.replicate (m * 2 ^ (n + 1)) b)) tC []
  | 0, s, h => by
    rw [dbl, dbl, run_seq, run_nop, run_app T T b hT, h, List.length_replicate,
      List.replicate_append_replicate]
    congr 3; ring
  | n + 1, s, h => by
    rw [dbl, run_seq, run_dbl T b hT m n s h, run_app T T b hT]
    have e1 : Function.update (Function.update s T (List.replicate (m * 2 ^ (n + 1)) b)) tC [] T =
        List.replicate (m * 2 ^ (n + 1)) b := by
      rw [Function.update_of_ne hT, Function.update_self]
    rw [e1, List.length_replicate, List.replicate_append_replicate,
      show m * 2 ^ (n + 1) + m * 2 ^ (n + 1) = m * 2 ^ (n + 1 + 1) by ring]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem run_dbl' (T : Fin K) (b : Bool) (hT : T ≠ tC) (n : ℕ) (s : Store K) :
    run (dbl T b (n + 1)) s = Function.update (Function.update s T
      (s T ++ List.replicate ((s T).length * (2 ^ (n + 1) - 1)) b)) tC [] := by
  induction n generalizing s with
  | zero =>
    rw [dbl, dbl, run_seq, run_nop, run_app T T b hT]; simp
  | succ n ih =>
    rw [dbl, run_seq, ih, run_app T T b hT]
    have e1 : Function.update (Function.update s T
        (s T ++ List.replicate ((s T).length * (2 ^ (n + 1) - 1)) b)) tC [] T =
        s T ++ List.replicate ((s T).length * (2 ^ (n + 1) - 1)) b := by
      rw [Function.update_of_ne hT, Function.update_self]
    rw [e1]
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have e2 : s T ++ List.replicate ((s T).length * (2 ^ (n + 1) - 1)) b ++
        List.replicate (s T ++ List.replicate ((s T).length * (2 ^ (n + 1) - 1)) b).length b =
        s T ++ List.replicate ((s T).length * (2 ^ (n + 1 + 1) - 1)) b := by
      rw [List.append_assoc, List.replicate_append_replicate]
      congr 2
      simp only [List.length_append, List.length_replicate, pow_succ]
      rcases (s T).length with _ | L
      · simp
      · have : (L + 1) * (2 ^ n * 2 - 1) + (L + 1 + (L + 1) * (2 ^ n * 2 - 1)) =
            (L + 1) * (2 ^ n * 2 * 2 - 1) := by
          have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          zify [h1, show 1 ≤ 2 ^ n * 2 by omega, show 1 ≤ 2 ^ n * 2 * 2 by omega]
          ring
        omega
    rw [e2]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem hot_zero : hot W 0 = List.replicate 4224 false ++ [true] := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp only [length_hot, W] at h1 ⊢
  simp only [hot, List.getElem_ofFn]
  by_cases hi : i < 4224
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate]
    simp only [decide_eq_false_iff_not]; omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem_singleton, decide_eq_true_eq]; omega

theorem hot_129 : hot W 129 = List.replicate 4095 false ++ [true] ++ List.replicate 129 false := by
  rw [List.append_assoc]
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp only [length_hot, W] at h1 ⊢
  simp only [hot, List.getElem_ofFn]
  by_cases hi : i < 4095
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate]
    simp only [decide_eq_false_iff_not]; omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases hi' : i = 4095
    · subst hi'; simp
    · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
      simp only [decide_eq_false_iff_not]; omega

/-! ### The pieces of the setup -/

theorem upd2_eq (s : Store K) (T : Fin K) (hT : T ≠ tC) (a b : List Bool) :
    Function.update (Function.update (Function.update (Function.update s T a) tC []) T b) tC [] =
      Function.update (Function.update s T b) tC [] := by
  funext t; simp only [Function.update_apply]; split_ifs <;> simp_all

theorem upd_tC_out (X : Store K) (T : Fin K) (h : T ≠ tC) (b : List Bool) :
    Function.update (Function.update X tC []) T b = Function.update (Function.update X T b) tC [] :=
  Function.update_comm (Ne.symm h) _ _ _

theorem vTG : List.replicate 4096 true ++ List.replicate 128 true ++ [true] = List.replicate W true := by
  rw [List.replicate_append_replicate, ← List.replicate_succ']

theorem vTA : List.replicate 4096 false ++ List.replicate 128 false ++ [true] = hot W 0 := by
  rw [List.replicate_append_replicate, hot_zero]

theorem vTP : (List.replicate 4096 false).tail ++ [true] ++ List.replicate 128 false ++ [false] =
    hot W 129 := by
  rw [hot_129, List.tail_replicate, List.append_assoc _ (List.replicate 128 false),
    ← List.replicate_succ']

theorem vOne : (List.replicate 128 false).tail ++ [true] = one128 := by
  rw [List.tail_replicate]; rfl

theorem run_sH (s : Store K) (h : s tH = []) :
    run sH s = Function.update (Function.update s tH (List.replicate 128 true)) tC [] := by
  rw [sH, run_seq, run_prim, Prim.apply, h, run_dbl tH true (by decide) 1 6 _ (by simp)]
  simp only [Function.update_idem]; rfl

theorem run_sQ (s : Store K) (h : s tQ = []) :
    run sQ s = Function.update (Function.update s tQ (List.replicate 4096 true)) tC [] := by
  rw [sQ, run_seq, run_prim, Prim.apply, h, run_dbl tQ true (by decide) 1 11 _ (by simp)]
  simp only [Function.update_idem]; rfl

theorem run_sT16 (s : Store K) (h : s tT16 = []) :
    run sT16 s = Function.update (Function.update s tT16 (List.replicate 65536 true)) tC [] := by
  rw [sT16, run_seq, run_prim, Prim.apply, h, run_dbl tT16 true (by decide) 1 15 _ (by simp)]
  simp only [Function.update_idem]; rfl

theorem run_sTG (s : Store K) (h : s tTG = []) (hQ : s tQ = List.replicate 4096 true)
    (hH : s tH = List.replicate 128 true) :
    run sTG s = Function.update (Function.update s tTG (List.replicate W true)) tC [] := by
  rw [sTG, run_seq, run_seq, run_app _ _ _ (by decide), run_app _ _ _ (by decide), run_prim,
    Prim.apply]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne, h, hQ, hH,
    List.length_replicate, List.nil_append]
  simp (disch := decide) only [upd_tC_out, Function.update_idem]
  first | rw [vTG] | rw [vTA] | rw [vTP] | rw [vOne]

theorem run_sTA (s : Store K) (h : s tTA = []) (hQ : s tQ = List.replicate 4096 true)
    (hH : s tH = List.replicate 128 true) :
    run sTA s = Function.update (Function.update s tTA (hot W 0)) tC [] := by
  rw [sTA, run_seq, run_seq, run_app _ _ _ (by decide), run_app _ _ _ (by decide), run_prim,
    Prim.apply]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne, h, hQ, hH,
    List.length_replicate, List.nil_append]
  simp (disch := decide) only [upd_tC_out, Function.update_idem]
  first | rw [vTG] | rw [vTA] | rw [vTP] | rw [vOne]

theorem run_sTP (s : Store K) (h : s tTP = []) (hQ : s tQ = List.replicate 4096 true)
    (hH : s tH = List.replicate 128 true) :
    run sTP s = Function.update (Function.update s tTP (hot W 129)) tC [] := by
  rw [sTP, run_seq, run_seq, run_seq, run_seq, run_app _ _ _ (by decide), run_tail, run_prim,
    Prim.apply, run_app _ _ _ (by decide), run_prim, Prim.apply]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne, h, hQ, hH,
    List.length_replicate, List.nil_append]
  simp (disch := decide) only [upd_tC_out, Function.update_idem]
  first | rw [vTG] | rw [vTA] | rw [vTP] | rw [vOne]

theorem run_sX (s : Store K) (h : s tX = []) (hH : s tH = List.replicate 128 true) :
    run sX s = Function.update (Function.update s tX (List.replicate 128 false)) tC [] := by
  rw [sX, run_app _ _ _ (by decide)]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne, h, hH,
    List.length_replicate, List.nil_append]

theorem run_sOne (s : Store K) (h : s tOne = []) (hH : s tH = List.replicate 128 true) :
    run sOne s = Function.update (Function.update s tOne one128) tC [] := by
  rw [sOne, run_seq, run_seq, run_app _ _ _ (by decide), run_tail, run_prim, Prim.apply]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne, h, hH,
    List.length_replicate, List.nil_append]
  simp (disch := decide) only [upd_tC_out, Function.update_idem]
  first | rw [vTG] | rw [vTA] | rw [vTP] | rw [vOne]

/-- The store after the setup. -/
theorem run_setup (x : List Bool) :
    let s := run setup (inputStore tI x)
    s tI = x ∧ s tTt = [true] ∧ s tTf = [false] ∧ s tTG = List.replicate W true ∧
      s tTA = hot W 0 ∧ s tTP = hot W 129 ∧ s tX = List.replicate 128 false ∧ s tOne = one128 ∧
      s tT16 = List.replicate 65536 true ∧ s fres = [false] ∧ s tO = [] := by
  intro s
  have hs : s = run setup (inputStore tI x) := rfl
  rw [setup] at hs
  simp only [run_seq, run_prim, Prim.apply] at hs
  rw [run_sH, run_sQ, run_sTG, run_sTA, run_sTP, run_sX, run_sOne, run_sT16] at hs
  all_goals try (simp (disch := decide) only [Function.update_of_ne, Function.update_self,
    inputStore, List.nil_append]; done)
  rw [hs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [Function.update_of_ne, Function.update_self, inputStore, List.nil_append]

end SigabaNeo.Tape.BF

/-!
# The brute-force `Enc` program: its output
-/


namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog
open Turing.MultiTapeTM

theorem run_output (s : Store K) (β r : Bool) (hO : s tO = []) (hb : s fbeta = [β])
    (hr : s fres = [r]) : run output s tO = [true, β && r, false] := by
  cases β <;> cases r <;>
    simp (disch := decide) [output, run_ifBit, run_prim, Prim.apply, Function.update_of_ne, hO, hb, hr]

/-- The input of `Enc` on a gate list. -/
def encInput (pw : List Bool) (gs : GateList) (β : Bool) : List Bool :=
  SigabaNeo.encodeTuple [pw, encGates gs, [β]]

theorem σFin_spec (pw : List Bool) (gs : GateList) (hgs : ∀ g ∈ gs, g.1 < W ∧ g.2 < W) (β : Bool)
    (X : List Bool) :
    (σFin (encInput pw gs β) X).last = evalGates (List.ofFn (xOf 128 X), gs) ∧
      (σFin (encInput pw gs β) X).beta = β := by
  have h := foldl_step1_input pw gs hgs β (σInit X) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h.1, h.2⟩

theorem exists_X_iff (gs : GateList) :
    (∃ X : List Bool, X.length = 128 ∧ evalGates (List.ofFn (xOf 128 X), gs) = true) ↔
      ∃ y : Fin 128 → Bool, evalGates (List.ofFn y, gs) = true := by
  constructor
  · rintro ⟨X, _, h⟩; exact ⟨_, h⟩
  · rintro ⟨y, h⟩
    refine ⟨List.ofFn (fun j : Fin 128 => y ⟨127 - j.val, by omega⟩), by simp, ?_⟩
    have e : xOf 128 (List.ofFn (fun j : Fin 128 => y ⟨127 - j.val, by omega⟩)) = y := by
      funext i
      simp only [xOf]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      congr 1; ext; simp; omega
    rw [e]; exact h

/-- **The output of the `Enc` program.** -/
theorem run_encProg (pw : List Bool) (gs : GateList) (hgs : ∀ g ∈ gs, g.1 < W ∧ g.2 < W)
    (β : Bool) :
    run encProg (inputStore tI (encInput pw gs β)) tO =
      [true, β && decide (∃ y : Fin 128 → Bool, evalGates (List.ofFn y, gs) = true), false] := by
  generalize hx : encInput pw gs β = x
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := run_setup x
  generalize hs1 : run setup (inputStore tI x) = s1 at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have g1 : GoodN x s1 := ⟨⟨h1, h2, h3, h4, h5, h6, by rw [h7]; rfl⟩, h9, h8, ⟨false, h10⟩, h11⟩
  have hβ : ∀ X, (σFin x X).beta = β := fun X => hx ▸ (σFin_spec pw gs hgs β X).2
  obtain ⟨n1, _, n3, n4⟩ := run_nest hβ 8 le_rfl s1 g1
  obtain ⟨r, hr⟩ := n1.res
  rw [encProg, run_seq, run_seq, hs1, run_output _ β r n1.out n4 hr]
  rw [hr, h10, h7] at n3
  simp only [hd, List.headD_cons, Bool.false_or] at n3
  rw [n3]
  congr 2
  rw [show (65536 : ℕ) ^ 8 = 2 ^ 128 by norm_num]
  have := orIter_all x
  simp only [← hx, fun X => (σFin_spec pw gs hgs β X).1] at this
  have e : orIter x (2 ^ 128) (List.replicate 128 false) =
      decide (∃ y : Fin 128 → Bool, evalGates (List.ofFn y, gs) = true) := by
    rw [Bool.eq_iff_iff, ← hx, this, decide_eq_true_iff, exists_X_iff]
  rw [e]

end SigabaNeo.Tape.BF

namespace SigabaNeo.Tape.BF

open Prog
open scoped Prog
open Turing.MultiTapeTM

theorem run_decProg (u : List Bool) (b : Bool) :
    run decProg (inputStore 0 (u ++ [true, b, false])) 1 = [true, b, false] := by
  simp only [decProg, run_seq, run_prim, Prim.apply,
    run_moveBits (1 : Fin 3) 0 2 (by decide) (by decide) (by decide)]
  simp [inputStore, Function.update_apply]

end SigabaNeo.Tape.BF


namespace AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit

open SigabaNeo SigabaNeo.Tape Turing.MultiTapeTM

/-! ### Input lengths -/

theorem length_encGates (gs : GateList) :
    (encGates gs).length = (gs.map fun g => 2 * (2 * g.1 + 1 + g.2) + 1).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [encGates, encList_cons, List.length_append, length_frame, encGate, encPair_apply,
      encUnary_apply, List.length_replicate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem length_circuit (φ : Circuit inputs size) : (encGates φ.gates).length ≤ 103821312 := by
  rw [length_encGates]
  have hb : ∀ y ∈ (φ.gates.map fun g => 2 * (2 * g.1 + 1 + g.2) + 1), y ≤ 25347 := by
    intro y hy
    simp only [Circuit.gates, List.map_ofFn, List.mem_ofFn, Function.comp] at hy
    obtain ⟨i, rfl⟩ := hy
    have h1 := (φ i).1.isLt
    have h2 := (φ i).2.isLt
    simp only [inputs, size] at h1 h2
    omega
  have := List.sum_le_length_nsmul _ 25347 hb
  have hl : φ.gates.length = 4096 := by rw [Circuit.gates, List.length_ofFn]; rfl
  rw [List.length_map, hl, smul_eq_mul] at this
  omega

theorem length_pw : (paramsWord Rel params).length = 515 := by
  simp [paramsWord, params, encodeTuple, encList, encBits, Rel, relation]

theorem gates_lt (φ : Circuit inputs size) : ∀ g ∈ φ.gates, g.1 < BF.W ∧ g.2 < BF.W := by
  intro g hg
  simp only [Circuit.gates, List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  exact ⟨(φ i).1.isLt, (φ i).2.isLt⟩

/-! ### The algorithms -/

theorem encodeTuple_bit (b : Bool) : encodeTuple [[b]] = [true, b, false] := rfl

/-- Satisfiability, decided by exhaustive search. -/
def satB (φ : Circuit inputs size) : Bool :=
  decide (∃ y : Fin 128 → Bool, evalGates (List.ofFn y, φ.gates) = true)

theorem satB_iff (φ : Circuit inputs size) : satB φ = true ↔ Rel.InL φ := by
  unfold satB
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩

theorem encM_run (φ : Circuit inputs size) (β : Bool) :
    encM.run (encodeTuple (paramsWord Rel params :: [encCircuit inputs size φ, encBit β])) =
      PMF.pure (encodeTuple [[β && satB φ]]) := by
  have hx : encodeTuple (paramsWord Rel params :: [encCircuit inputs size φ, encBit β]) =
      BF.encInput (paramsWord Rel params) φ.gates β := by
    rw [BF.encInput]; rfl
  have hlen : (BF.encInput (paramsWord Rel params) φ.gates β).length ≤ nE := by
    have := length_circuit φ
    rw [BF.encInput, BF.encodeTuple_three, List.length_append, List.length_append, length_frame,
      length_frame, length_frame, length_pw, List.length_singleton]
    unfold nE
    omega
  rw [hx, encM, XProg.run_toMachineT _ wf_enc _ _ _ _ hlen, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_enc, PMF.pure_map]
  have h := BF.run_encProg (paramsWord Rel params) φ.gates (gates_lt φ) β
  rw [h, encodeTuple_bit]
  unfold satB
  exact rfl

theorem decM_run (φ : Circuit inputs size) (w : Fin inputs → Bool) (b : Bool) :
    decM.run (encodeTuple (paramsWord Rel params ::
      [encCircuit inputs size φ, encAssignment inputs w, encBit b])) =
      PMF.pure (encodeTuple [[b]]) := by
  have hx : encodeTuple (paramsWord Rel params ::
      [encCircuit inputs size φ, encAssignment inputs w, encBit b]) =
      (frame (paramsWord Rel params) ++ frame (encGates φ.gates) ++ frame (List.ofFn w)) ++
        [true, b, false] := by
    simp [encodeTuple, encList, encBits, encCircuit, encAssignment, encBit, frame]
  have hlen : ((frame (paramsWord Rel params) ++ frame (encGates φ.gates) ++ frame (List.ofFn w)) ++
        [true, b, false]).length ≤ nD := by
    have := length_circuit φ
    simp only [List.length_append, length_frame, length_pw, List.length_ofFn, List.length_cons,
      List.length_nil, nD, inputs]
    omega
  rw [hx, decM, XProg.run_toMachineT _ wf_dec _ _ _ _ hlen, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_dec, PMF.pure_map, BF.run_decProg, encodeTuple_bit]

/-! ### The propositions -/

theorem impl_enc : impl.machine Alg.enc = encM := by simp [impl]

theorem impl_dec : impl.machine Alg.dec = decM := by simp [impl, Alg.enc, Alg.dec]

theorem enc_eq (φ : Circuit inputs size) (β : Bool) :
    WE.enc (R := Rel) params impl φ β = PMF.pure (encBit (β && satB φ)) := by
  show (((impl.machine Alg.enc).run (encodeTuple (paramsWord Rel params ::
    [encCircuit inputs size φ, encBit β]))).map _).map _ = _
  rw [impl_enc, encM_run, PMF.pure_map, PMF.pure_map]
  rw [show (WE.sig Alg.enc).outputs.length = [[β && satB φ]].length from rfl,
    decodeTuple_encodeTuple]
  rfl

theorem dec_eq (φ : Circuit inputs size) (w : Fin inputs → Bool) (b : Bool) :
    WE.dec (R := Rel) params impl φ w (encBit b) = PMF.pure (encBit b) := by
  show (((impl.machine Alg.dec).run (encodeTuple (paramsWord Rel params ::
    [encCircuit inputs size φ, encAssignment inputs w, encBit b]))).map _).map _ = _
  rw [impl_dec, decM_run, PMF.pure_map, PMF.pure_map]
  rw [show (WE.sig Alg.dec).outputs.length = [[b]].length from rfl, decodeTuple_encodeTuple]
  rfl

theorem correct : WE.Correct Rel params impl := by
  intro (φ : Circuit inputs size) (w : Fin inputs → Bool) hw β
  have hs : satB φ = true := (satB_iff φ).mpr ⟨w, hw⟩
  unfold WE.decryptLaw
  rw [enc_eq, hs, Bool.and_true, PMF.pure_bind, dec_eq, PMF.pure_apply_self, ENNReal.toReal_one]
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ params.corrBits)⁻¹ := by positivity
  linarith

theorem falseStatementSecure : WE.FalseStatementSecure Rel params impl := by
  intro (φ : Circuit inputs size) hφ A
  have hs : satB φ = false := by
    cases h : satB φ
    · rfl
    · exact absurd ((satB_iff φ).mp h) hφ
  have h : WE.challenge Rel params impl φ false = WE.challenge Rel params impl φ true := by
    unfold WE.challenge
    rw [enc_eq, enc_eq, hs, Bool.and_false, Bool.and_false]
  rw [h]
  simp only [Problem.gain, sub_self]
  simp

/-! ### The cost -/

/-- The time bound of the `Enc` program, certified by the numeric interpreter. -/
def TE : ℕ := 381461057563519853491131165267976641333226266624117730554

/-- The per-tape bounds after the `Enc` program. -/
def claimE : List ℕ := [207643659, 3, 65536, 1, 1, 128, 4096, 4225, 4225, 4225, 128, 128, 4225,
  4225, 4225, 207643659, 207643659, 0, 0, 128, 128, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 32768, 65536,
  65536, 65536, 65536, 65536, 65536, 65536, 65536]

theorem check_enc : NB.check 3 BF.encProg [207643659] claimE TE = true := by
  decide +kernel

/-- The time bound of the `Dec` program. -/
def TD : ℕ := 258695979056124760

theorem check_dec : NB.check 3 BF.decProg [207643916] [207643916, 3, 207643916] TD = true := by
  decide +kernel

theorem inputBound_le {k : ℕ} (i₀ : Fin k) (hi : i₀.val = 0) (n : ℕ) :
    Prog.inputBound i₀ n ≤ NB.vg [n] := by
  intro t
  simp only [Prog.inputBound, Function.update_apply, NB.vg]
  split_ifs with h
  · subst h; simp [hi]
  · exact Nat.zero_le _

/-- The description length of `Enc`. -/
def DE : ℕ := 6 * 9842 * 3 ^ 40 * 178

/-- The description length of `Dec`. -/
def DD : ℕ := 6 * 368 * 3 ^ 3 * 25

theorem lenBoundT_prog {k : ℕ} (p : Prog k) (ℓ : Fin k → ℕ) :
    XProg.lenBoundT (XProg.prog p) ℓ = p.lenBoundT ℓ := rfl

theorem totalTime_le {k : ℕ} (p : Prog k) (i₀ o : Fin k) (n T L : ℕ)
    (ht : p.timeBoundT (Prog.inputBound i₀ n) ≤ T) (hl : p.lenBoundT (Prog.inputBound i₀ n) o ≤ L) :
    XProg.totalTimeT (XProg.prog p) i₀ o n ≤ (2 * n + 2) + T + (2 * L + 2) := by
  unfold XProg.totalTimeT
  rw [XProg.timeBoundT_prog, lenBoundT_prog]
  omega

theorem cost_bound {k : ℕ} (p : Prog k) (i₀ o : Fin k) (n C S D : ℕ)
    (hcard : Fintype.card (XProg.prog p).State = S)
    (htot : XProg.totalTimeT (XProg.prog p) i₀ o n ≤ C)
    (hD : 6 * (S + 4) * 3 ^ k * 3 ^ 0 * Machine.entryBits k (S + 4) 0 = D) :
    (XProg.toMachineT (XProg.prog p) i₀ o n).cost ≤ C + D := by
  rw [XProg.cost_toMachineT, hcard, hD]
  exact Nat.add_le_add_right htot _

theorem cost_encM : encM.cost ≤ (2 * nE + 2) + TE + (2 * 3 + 2) + DE := by
  obtain ⟨hl, ht⟩ := NB.bounds_of_check check_enc (inputBound_le BF.tI rfl nE)
  have hcard : Fintype.card (XProg.prog BF.encProg).State = 9838 := by
    rw [XProg.card_state, XProg.size_prog]; decide
  have he0 : Machine.entryBits 40 (9838 + 4) 0 = 178 := by decide +kernel
  have he : 6 * (9838 + 4) * 3 ^ 40 * 3 ^ 0 * Machine.entryBits 40 (9838 + 4) 0 = DE := by
    rw [he0, DE]; norm_num
  exact cost_bound BF.encProg BF.tI BF.tO nE _ 9838 DE hcard
    (totalTime_le BF.encProg BF.tI BF.tO nE TE 3 ht (hl BF.tO)) he

theorem cost_decM : decM.cost ≤ (2 * nD + 2) + TD + (2 * 3 + 2) + DD := by
  obtain ⟨hl, ht⟩ := NB.bounds_of_check check_dec (inputBound_le (0 : Fin 3) rfl nD)
  have hcard : Fintype.card (XProg.prog BF.decProg).State = 364 := by
    rw [XProg.card_state, XProg.size_prog]; decide
  have he0 : Machine.entryBits 3 (364 + 4) 0 = 25 := by decide +kernel
  have he : 6 * (364 + 4) * 3 ^ 3 * 3 ^ 0 * Machine.entryBits 3 (364 + 4) 0 = DD := by
    rw [he0, DD]; norm_num
  exact cost_bound BF.decProg 0 1 nD _ 364 DD hcard
    (totalTime_le BF.decProg 0 1 nD TD 3 ht (hl 1)) he

theorem N_eq : (2 * nE + 2) + TE + (2 * 3 + 2) + DE + ((2 * nD + 2) + TD + (2 * 3 + 2) + DD) = N := by
  simp only [nE, nD, TE, TD, DE, DD, N]; norm_num

theorem cost_eq_gen (m1 m2 : Machine) :
    m1.time + m2.time + (m1.descLen + m2.descLen) = m1.cost + m2.cost := by
  unfold Machine.cost; omega

theorem wecost_gen (i : Impl WE.sig) :
    WE.cost i = (i.machine Alg.enc).cost + (i.machine Alg.dec).cost := by
  unfold WE.cost Machine.cost; omega

theorem cost_eq : WE.cost impl = encM.cost + decM.cost := by
  rw [wecost_gen, impl_enc, impl_dec]

theorem cost_le : WE.cost impl ≤ N := by
  rw [cost_eq, ← N_eq]
  exact Nat.add_le_add cost_encM cost_decM

/-- The Submission proposition from the two propositions and the cost bound, for any
submission. -/
theorem spec_of (v : Submission P R) (hC : WE.Correct Rel params v.impl)
    (hF : WE.FalseStatementSecure Rel params v.impl) (hc : WE.cost v.impl ≤ v.N) :
    SubmissionProp v := by
  refine ⟨fun (i : Fin 2) _ => ?_, hc⟩
  fin_cases i
  · exact hC
  · exact hF

/-- **The Submission proposition of the explicit brute-force submission.** -/
theorem submissionProp_explicit : SubmissionProp u :=
  spec_of u correct falseStatementSecure cost_le

end AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit

theorem solution :
    AdvancedEncryption.WE.CircuitSAT.SubmissionProp
      AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit.u :=
  AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit.submissionProp_explicit
