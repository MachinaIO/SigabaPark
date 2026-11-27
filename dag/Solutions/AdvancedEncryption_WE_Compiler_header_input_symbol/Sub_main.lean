import SigabaNeo.Trusted.Machine

open Turing

theorem solution {k l : ℕ} {Q Q' : Type} (src dst z : List Bool)
    (c : Cfg k Bool Q (src ++ z)) (e : Cfg l Bool Q' (dst ++ z))
    (hp : e.inputPos.val = dst.length + 1 + (c.inputPos.val - (src.length+1))) :
    let i := min c.inputPos.val (src.length+1)
    (if i = src.length+1 then e.inputSymbol else if i=0 then none else src[i-1]?) =
      c.inputSymbol := by
  let j := c.inputPos.val
  have hj : j ≤ src.length + z.length + 1 := by
    have := c.inputPos.isLt
    simp only [List.length_append] at this
    dsimp [j]; omega
  have read {kk : ℕ} {T : Type} {s : List Bool} (cfg : Cfg kk Bool T s) :
      cfg.inputSymbol = if cfg.inputPos.val = 0 then none else s[cfg.inputPos.val-1]? := by
    unfold Cfg.inputSymbol
    split_ifs with h h'
    all_goals first | rfl | (simp_all [Fin.ext_iff])
  dsimp only
  rw [read c,read e]
  change (if min j (src.length+1)=src.length+1 then _ else _) = if j=0 then _ else _
  by_cases ht : src.length+1 ≤ j
  · rw [min_eq_right ht,ite_eq_left rfl]
    have hn : j ≠ 0 := by omega
    rw [ite_eq_right hn,ite_eq_right (show e.inputPos.val ≠ 0 by omega)]
    rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega)]
    congr 1
    dsimp [j] at *
    omega
  · rw [min_eq_left (by omega),ite_eq_right (by omega : j ≠ src.length+1)]
    split_ifs
    · rfl
    · rw [List.getElem?_append_left (by omega)]
