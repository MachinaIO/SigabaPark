import Definitions.Def_FixedHeaderTrace
import Theorems.Thm_AdvancedEncryption_WE_Compiler_header_input_symbol

open SigabaNeo SigabaNeo.Machine SigabaNeo.Machine.Header Turing Turing.MultiTapeMachine
open AdvancedEncryption.WE.Compiler

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
theorem solution (A : Machine) (src dst z : List Bool) (c : ConfigOf A (src++z)) (coin : Bool) :
    tick (A.fixedHeaderMachine src dst.length) (embed A src dst z c) coin =
      embed A src dst z (tick A c coin) := by
  have motionLemma {a b n h1 h2 : ℕ} (v : Fin (h1+2)) (w : Fin (h2+2)) (m : SignType)
      (marker blank : Bool) (len1 : h1=a+n) (len2 : h2=b+n) (hp : w.val=b+1+(v.val-(a+1)))
      (hm : marker=decide (v.val-(a+1)=0)) (hb : blank=decide (w.val=b+n+1)) :
      let tag := min v.val (a+1)
      let tail := decide (tag=a+1)
      let back := tail && (m == -1) && marker
      let motion : SignType := if !tail || back || (m == 1 && blank) then 0 else m
      let next := (moveInputPos v m).val
      min (if tail then (if back then a else a+1) else
        if m == -1 then tag-1 else if m == 1 then tag+1 else tag) (a+1) = min next (a+1) ∧
        ((v.val-(a+1):ℕ):ℤ)+motion.cast=((next-(a+1):ℕ):ℤ) ∧
        (moveInputPos w motion).val=b+1+(next-(a+1)) := by
    subst h1; subst h2; subst marker; subst blank
    dsimp only
    have hv := v.isLt
    have moveVal {h : ℕ} (pos : Fin (h+2)) (m : SignType) :
        (moveInputPos pos m).val = if m = -1 then pos.val-1 else
          if m = 1 then min (pos.val+1) (h+1) else pos.val := by
      have he := val_moveInputPos_eq pos m
      have bd := pos.isLt
      cases m <;> simp [SignType.cast] at he ⊢ <;> omega
    simp only [moveVal]
    cases m <;> simp <;> split_ifs <;> simp_all <;> omega
  let e := embed A src dst z c
  have hr := header_input_symbol src dst z c.tapes e.tapes rfl
  dsimp only at hr
  have hw : (fun i : Fin A.tapes => e.tapes.workTapeSymbols i.castSucc) = c.tapes.workTapeSymbols := by
    funext i
    simp [e, embed, Cfg.workTapeSymbols, Fin.lastCases_castSucc]
  cases hq : c.tapes.state with
  | none => simp [tick, embed, hq]
  | some q =>
    change tick _ e _ = _
    have he : e.tapes.state = some (finSumFinEquiv (.inr (finProdFinEquiv
        (q,(⟨min c.tapes.inputPos.val (src.length+1),by omega⟩ : Fin (src.length+2)))))) := by
      simp [e, embed,hq]
    unfold tick
    rw [he,hq]
    simp only [fixedHeaderMachine, Equiv.symm_apply_apply, decide_eq_true_eq]
    erw [hr,hw]
    cases hact : A.machine.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols Fin.elim0 coin with
    | query o _ => exact Fin.elim0 o
    | step act qs moves =>
      dsimp only
      let j := c.tapes.inputPos.val
      let a := src.length
      let tag := min j (a+1)
      let off := j-(a+1)
      let tail := decide (tag=a+1)
      let m := act.inputTape
      let back := tail && (m == -1) && (e.tapes.workTapeSymbols (Fin.last A.tapes)).isSome
      let motion : SignType := if !tail || back || (m == 1 && e.tapes.inputSymbol.isNone) then 0 else m
      let newTag := min (if tail then (if back then a else a+1) else
        if m == -1 then tag-1 else if m == 1 then tag+1 else tag) (a+1)
      let next := (moveInputPos c.tapes.inputPos m).val
      have marker : (e.tapes.workTapeSymbols (Fin.last A.tapes)).isSome = decide (off=0) := by
        simp [e,embed,Cfg.workTapeSymbols,off,j,a]
        split_ifs with h <;> simp [h]
      have blank : e.tapes.inputSymbol.isNone = decide (e.tapes.inputPos.val=dst.length+z.length+1) := by
        have pos : e.tapes.inputPos.val = dst.length+1+off := rfl
        simp only [Cfg.inputSymbol]
        split_ifs with h h
        · have bad : e.tapes.inputPos.val = 0 := congrArg Fin.val h
          omega
        · simp only [List.length_append] at h
          simp [h]
        · have hh : e.tapes.inputPos.val ≠ dst.length+z.length+1 := by simpa only [List.length_append] using h
          simp [hh]
      have bounds := c.tapes.inputPos.isLt
      simp only [List.length_append] at bounds
      have phys : e.tapes.inputPos.val = dst.length+1+off := rfl
      have arith : newTag=min next (a+1) ∧
          ((off:ℤ)+motion.cast = ((next-(a+1):ℕ):ℤ)) ∧
          (moveInputPos e.tapes.inputPos motion).val=dst.length+1+(next-(a+1)) := by
        exact motionLemma c.tapes.inputPos e.tapes.inputPos m _ _ List.length_append
          List.length_append phys marker blank
      apply Config.ext
      · apply Cfg.ext
        · simp only [Config.step,Turing.Action.apply,embed]
          refine congrArg (fun v : Fin (a+2) => act.state.map (fun q =>
            (finSumFinEquiv (.inr (finProdFinEquiv (q,v))) : Fin ((dst.length+1)+A.states*(a+2))))) ?_
          apply Fin.ext
          simpa [newTag, next, tail, tag, j, a, back, m, decide_eq_true_eq] using arith.1
        · exact Fin.ext arith.2.2
        · funext i; refine Fin.lastCases ?_ (fun v => ?_) i
          · simp [Config.step,Turing.Action.apply,embed,e]
          · simp [Config.step,Turing.Action.apply,embed,e]
        · funext i; refine Fin.lastCases ?_ (fun v => ?_) i
          · simpa only [e,Config.step,Turing.Action.apply,embed,Fin.lastCases_last,off,next,j,a,motion,back,tail,tag,m,decide_eq_true_eq] using arith.2.1
          · simp [Config.step,Turing.Action.apply,embed,e]
        · rfl
      · exact Subsingleton.elim _ _
