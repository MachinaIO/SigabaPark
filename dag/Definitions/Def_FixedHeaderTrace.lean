import Definitions.Def_FixedHeaderMachine
open SigabaNeo Turing Turing.MultiTapeMachine

namespace SigabaNeo.Machine.Header
abbrev ConfigOf (A : Machine) (w : List Bool) :=
  Config A.tapes Bool (Fin A.states) (Fin 0) w

def tick (A : Machine) {w : List Bool} (c : ConfigOf A w) (coin : Bool) : ConfigOf A w :=
  match c.tapes.state with
  | none => c
  | some q =>
    match A.machine.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols Fin.elim0 coin with
    | .step act out mv => c.step act out mv
    | .query o _ => Fin.elim0 o

def embed (A : Machine) (src dst z : List Bool) (c : ConfigOf A (src++z)) :
    ConfigOf (A.fixedHeaderMachine src dst.length) (dst++z) := by
  let j := c.tapes.inputPos.val
  let off := j-(src.length+1)
  have hj := c.tapes.inputPos.isLt
  simp only [List.length_append] at hj
  let idx : Fin (src.length+2) := ⟨min j (src.length+1),by omega⟩
  refine ⟨⟨c.tapes.state.map (fun q => finSumFinEquiv (.inr (finProdFinEquiv (q,idx)))),
    ⟨dst.length+1+off,by dsimp [off,j]; simp only [List.length_append]; omega⟩,
    Fin.lastCases (fun x => if x=0 then some true else none) c.tapes.workTapes,
    Fin.lastCases (off : ℤ) c.tapes.workTapePos,c.tapes.output⟩,fun o => Fin.elim0 o⟩
end SigabaNeo.Machine.Header

namespace SigabaNeo.Machine.Header
def seek (A : Machine) (src dst z : List Bool) (i : Fin (dst.length+1)) :
    ConfigOf (A.fixedHeaderMachine src dst.length) (dst++z) :=
  ⟨⟨some (finSumFinEquiv (.inl i)),⟨1+i.val,by simp only [List.length_append]; omega⟩,
     fun _ _ => none,fun _ => 0,[]⟩,fun o => Fin.elim0 o⟩
end SigabaNeo.Machine.Header
