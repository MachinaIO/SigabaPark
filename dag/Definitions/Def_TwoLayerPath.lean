import SigabaNeo.Trusted.Machine
namespace TwoLayerPath
open SigabaNeo
/-- Coefficients of the two public residual polynomials, in degree order. -/
def output (d beta : Bool) (k i : Nat) : Bool :=
  let a := k.testBit 0
  let b := k.testBit 1
  let c := k.testBit 2
  let h := k.testBit 3
  let g := k.testBit 4
  [a,xor b beta,c,d && h,xor h (!d && g),xor h (xor a c),xor g b][i]?.getD false

def enc : Machine where
  tapes := 0
  states := 1920
  time := 14
  machine := {
    initial := ⟨0, by decide⟩
    tr := fun q inp _ _ coin => Id.run do
      let pc := q.val/128
      let old := q.val%128
      let d := if pc==0 then inp.getD false else old.testBit 6
      let beta := if pc==1 then inp.getD false else old.testBit 5
      let k := old%32 + (if 2<=pc && pc<7 && coin then 2^(pc-2) else 0)
      let target := (pc+1)*128+64*d.toNat+32*beta.toNat+k
      return .step {
        inputTape := if pc<2 then 1 else 0
        workTapes := Fin.elim0
        output := if pc>=7 then some (output d beta k (pc-7)) else none
        state := if h : target<1920 ∧ pc<13 then some ⟨target,h.1⟩ else none
      } Fin.elim0 Fin.elim0 }

def dec : Machine where
  tapes := 0
  states := 1088
  time := 135
  machine := {
    initial := ⟨0, by decide⟩
    tr := fun q inp _ _ _ => Id.run do
      let pc := q.val/8
      let u := xor (q.val.testBit 2) (pc<64 && inp.getD false)
      let v := xor (q.val.testBit 1) (64<=pc && pc<128 && inp.getD false)
      let i := pc-128
      let take := i==0 || i==3 || ((i==1 || i==4) && u) ||
                  ((i==2 || i==5) && v) || (i==6 && u && v)
      let z := xor (q.val.testBit 0) (128<=pc && take && inp.getD false)
      let target := 8*(pc+1)+4*u.toNat+2*v.toNat+z.toNat
      return .step {
        inputTape := 1
        workTapes := Fin.elim0
        output := if pc==134 then some z else none
        state := if h : target<1088 ∧ pc<134 then some ⟨target,h.1⟩ else none
      } Fin.elim0 Fin.elim0 }
end TwoLayerPath
