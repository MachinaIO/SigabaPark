import Definitions.Def_WE_UnaryTraceBlocks

open Turing SigabaNeo AdvancedEncryption.WE.UnaryTraceWalk

private theorem tick {x : List Bool} (c : Cfg 2 Bool State x) (j : ℕ) :
    tm.runFrom c (j + 1) = tm.step (tm.runFrom c j) := Function.iterate_succ_apply' _ _ _

theorem solution (x cert hist : List Bool) (p : ℕ) (v : Bool) :
    tm.runFrom (scanCfg x cert hist p 0 (.appendBit v)) (hist.length + 1) =
      if cert[hist.length]? = some v then
        scanCfg x cert (hist ++ [v]) p ((hist.length : ℤ) + 1) (.advance v)
      else { scanCfg x cert hist p hist.length (.appendBit v) with state := none, output := [false] } := by
  have scanned (j : ℕ) (hj : j ≤ hist.length) :
      tm.runFrom (scanCfg x cert hist p 0 (.appendBit v)) j =
        scanCfg x cert hist p j (.appendBit v) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [tick]
      rw [ih (by omega), tm.step_of_state (q := .inr (.appendBit v)) rfl]
      rw [tm, MultiTapeTM.tr_ofTr]
      have trEq : tr (.inr (.appendBit v)) (scanCfg x cert hist p j (.appendBit v)).inputSymbol
          (scanCfg x cert hist p j (.appendBit v)).workTapeSymbols = go (.appendBit v) 0 1 := by
        simp [tr, scanCfg, Cfg.workTapeSymbols, show j < hist.length by omega]
      rw [trEq]
      refine Cfg.ext rfl (by simp [go, act, Action.apply, scanCfg]) ?_ ?_ rfl
      · funext i
        simp [go, act, Action.apply, scanCfg]
      · funext i
        simp [go, act, Action.apply, scanCfg]
  rw [tick]
  rw [scanned _ le_rfl, tm.step_of_state (q := .inr (.appendBit v)) rfl, tm,
    MultiTapeTM.tr_ofTr]
  split
  next he =>
    have trEq : tr (.inr (.appendBit v))
        (scanCfg x cert hist p hist.length (.appendBit v)).inputSymbol
        (scanCfg x cert hist p hist.length (.appendBit v)).workTapeSymbols =
        act (some (.inr (.advance v))) 0 1 none (some v) := by
      simp [tr, scanCfg, Cfg.workTapeSymbols, he]
    rw [trEq]
    refine Cfg.ext rfl (by simp [act, Action.apply, scanCfg]) ?_ rfl rfl
    funext i
    by_cases hi : i = 0
    · simp [act, Action.apply, scanCfg, hi]
    · simp [act, Action.apply, scanCfg, hi, tapeOfList_append_single]
  next he =>
    have trEq : tr (.inr (.appendBit v))
        (scanCfg x cert hist p hist.length (.appendBit v)).inputSymbol
        (scanCfg x cert hist p hist.length (.appendBit v)).workTapeSymbols = finish false := by
      simp [tr, scanCfg, Cfg.workTapeSymbols, he]
    rw [trEq]
    refine Cfg.ext rfl (by simp [finish, act, Action.apply, scanCfg]) ?_ ?_ rfl
    · funext i
      simp [finish, act, Action.apply, scanCfg]
    · funext i
      simp [finish, act, Action.apply, scanCfg]
