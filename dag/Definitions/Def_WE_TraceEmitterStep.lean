import Definitions.Def_WE_TraceEmitterState

open Turing SigabaNeo AdvancedEncryption.WE.TraceEmitter

namespace AdvancedEncryption.WE.TraceEmitter

def appendOption (xs : List Bool) (o : Option Bool) := xs ++ o.toList

theorem tapeUpdate (xs : List Bool) (z : ℤ) (o : Option Bool)
    (hz : ∀ b, o = some b → z = xs.length) :
    (match o.map some with
      | none => tapeOfList xs
      | some b => Function.update (tapeOfList xs) z b) = tapeOfList (appendOption xs o) := by
  cases o with
  | none => simp [appendOption]
  | some b =>
    rw [hz b rfl]
    simp [appendOption, tapeOfList_append_single]

/-- Check one physical tick against an explicit transition. Every requested write is an append. -/
theorem tick {x : List Bool} {p : ℕ} {s h : List Bool} {z j : ℤ} {q : Phase}
    {out : List Bool} {q' : Option Phase} {move : Bool} {ds dh : SignType}
    {sw hw emit : Option Bool}
    (inside : p + move.toNat ≤ x.length)
    (ht : tr q x[p]? (fun t ↦ if t = 0 then tapeOfList s z else if t = 1 then
        tapeOfList h j else tapeOfList [true] j) =
      action q' (if move then 1 else 0) ds dh sw hw none emit)
    (hs : ∀ b, sw = some b → z = s.length) (hh : ∀ b, hw = some b → j = h.length) :
    tm.step (snap x p s h z j (some q) out) =
      snap x (p+move.toNat) (appendOption s sw) (appendOption h hw)
        (z + ds.cast) (j + dh.cast) q' (appendOption out emit) := by
  have hp : p ≤ x.length := by omega
  have hi : (snap x p s h z j (some q) out).inputSymbol = x[p]? := by
    by_cases lt : p < x.length
    · rw [inputSymbolInner p (by simp [snap, min_eq_left hp, Nat.add_comm]) lt, List.getElem?_eq_getElem lt]
    · have ep : p = x.length := by omega
      subst p
      simp [Cfg.inputSymbol, snap]
  have hwk : (snap x p s h z j (some q) out).workTapeSymbols =
      fun t ↦ if t = 0 then tapeOfList s z else if t = 1 then tapeOfList h j
        else tapeOfList [true] j := by
    funext t
    by_cases a : t = 0 <;> by_cases b : t = 1 <;> simp [Cfg.workTapeSymbols, snap, a, b]
  rw [tm.step_of_state (q := q) rfl, tm, MultiTapeTM.tr_ofTr, hi, hwk, ht]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    cases move with
    | false => simp [Action.apply, action, snap]
    | true =>
      change p + 1 ≤ x.length at inside
      change (moveInputPos _ SignType.pos).val = _
      rw [moveInputPos_pos_of_ne_right _ (by simp [snap, min_eq_left hp]; omega)]
      simp [snap, min_eq_left hp, inside]
  · funext t
    by_cases a : t = 0
    · cases sw <;> simp_all [Action.apply, action, snap, appendOption, tapeOfList_append_single]
    · by_cases b : t = 1
      · cases hw <;> simp_all [Action.apply, action, snap, appendOption, tapeOfList_append_single]
      · simp [Action.apply, action, snap, a, b]
  · funext t
    by_cases a : t = 0 <;> by_cases b : t = 1 <;> simp [Action.apply, action, snap, a, b]

end AdvancedEncryption.WE.TraceEmitter
