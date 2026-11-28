import SigabaNeo.Trusted.Machine

namespace PinnedSeparator
open SigabaNeo

def masks (kind : Bool) : List Nat :=
  if kind then [1,131,261,1033,2065,545,4161,8,16,32,256,512,1024]
  else [1,131,517,2057,273,1057,4161,8,16,512,1024]

def enc : Machine where
  tapes := 1
  states := 1376
  time := 171
  machine := {
    initial := ⟨0, by decide⟩
    tr := fun q inp ws _ coin => Id.run do
      let pc := q.val / 8
      let kind := if pc == 0 then inp.getD false else q.val % 8 >= 4
      let beta := if pc == 1 then inp.getD false else q.val % 4 >= 2
      let acc := q.val % 2 == 1
      let row := (pc-15)/13
      let j := (pc-15)%13
      let idx := if row%2 == 0 then 12-j else j
      let bit := ws 0 |>.getD false
      let par := xor acc (bit && (((masks kind)[row+1]?.getD 0).testBit idx))
      let last := pc >= 15 && j == 12
      let done_ := last && row+2 == (masks kind).length
      let next := 8*(pc+1)+4*kind.toNat+2*beta.toNat+(pc>=15 && !last && par).toNat
      let mv : SignType := if pc<2 then 0 else if pc<14 then 1 else if pc==14 || last then 0 else if row%2==0 then -1 else 1
      let out := if pc==2 then some (xor beta coin) else if last then some par else none
      return .step {
        inputTape := if pc<2 then 1 else 0
        workTapes := fun _ => (if 2<=pc && pc<15 then some (some coin) else none, mv)
        output := out
        state := if h : next<1376 ∧ !done_ then some ⟨next,h.1⟩ else none
      } Fin.elim0 Fin.elim0 }

def dec : Machine where
  tapes := 0
  states := 4576
  time := 142
  machine := {
    initial := ⟨0, by decide⟩
    tr := fun q inp _ _ _ => Id.run do
      let pc := q.val/32
      let bit := inp.getD false
      let kind := if pc==0 then bit else q.val%32>=16
      let old := (q.val%16)/2
      let groupBit := if pc<=40 then 4 else if pc<=88 then 2 else 1
      let summary := if pc>=1 && pc<=128 && bit then old ||| groupBit else old
      let select : Nat := if summary==2 then 4233 else if summary==5 then 2593 else 0
      let par := xor (q.val%2==1) (kind && pc>=129 && bit && select.testBit (pc-129))
      let done_ := pc+1==129+(masks kind).length
      let next := 32*(pc+1)+16*kind.toNat+2*summary+par.toNat
      return .step {
        inputTape := 1
        workTapes := Fin.elim0
        output := if done_ then some par else none
        state := if h : next<4576 ∧ !done_ then some ⟨next,h.1⟩ else none
      } Fin.elim0 Fin.elim0 }

end PinnedSeparator
