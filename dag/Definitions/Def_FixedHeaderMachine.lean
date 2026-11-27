import SigabaNeo.Trusted.Machine

open SigabaNeo Turing

/-- Run the source attacker on a fixed virtual header and the unchanged physical suffix. -/
def SigabaNeo.Machine.fixedHeaderMachine (A : Machine) (src : List Bool) (skip : ℕ) : Machine := by
  let a := src.length
  let n := (skip + 1) + A.states * (a+2)
  let initCode (j : Fin (skip+1)) : Fin n := finSumFinEquiv (.inl j)
  let runCode (q : Fin A.states) (i : Fin (a+2)) : Fin n :=
    finSumFinEquiv (.inr (finProdFinEquiv (q,i)))
  refine ⟨A.tapes+1,n,⟨initCode 0,?_⟩,A.time+skip+1⟩
  intro st sym tapes _ coin
  let ret (move : SignType) (mark : Option (Option Bool) × SignType)
      (old : Fin A.tapes → Option (Option Bool) × SignType) (out : Option Bool)
      (next : Option (Fin n)) : MultiTapeMachine.Action (A.tapes+1) Bool (Fin n) (Fin 0) :=
    .step ⟨move,Fin.lastCases mark old,out,next⟩ Fin.elim0 Fin.elim0
  match finSumFinEquiv.symm st with
  | .inl j =>
    if h : j.val < skip then
      exact ret 1 (none,0) (fun _ => (none,0)) none (some (initCode ⟨j.val+1,by omega⟩))
    else
      exact ret 0 (some (some true),0) (fun _ => (none,0)) none
        (some (runCode A.machine.initial ⟨1,by omega⟩))
  | .inr j =>
    let qi : Fin A.states × Fin (a+2) := finProdFinEquiv.symm j
    let i := qi.2.val
    let tail := decide (i=a+1)
    let virtual := if tail then sym else if i=0 then none else src[i-1]?
    match A.machine.tr qi.1 virtual (fun v => tapes v.castSucc) Fin.elim0 coin with
    | .query impossible _ => exact Fin.elim0 impossible
    | .step action _ _ =>
      let m := action.inputTape
      let back := tail && (m == -1) && (tapes (Fin.last A.tapes)).isSome
      let realMove := if !tail || back || (m == 1 && sym.isNone) then 0 else m
      let virtualIndex := if tail then (if back then a else a+1)
        else if m == -1 then i-1 else if m == 1 then i+1 else i
      exact ret realMove (none,realMove) action.workTapes action.output
        (action.state.map fun q => runCode q ⟨min virtualIndex (a+1),by omega⟩)
