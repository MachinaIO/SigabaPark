import SigabaNeo.Trusted.Machine
namespace Original201
namespace CompactRowIssuer
open SigabaNeo

-- Tape 0 holds fixed-width secret residues, tape 1 the running sum, and tape 2 the row bodies.
structure Act where
  next : Nat := 1000000
  tape : Nat := 3
  write : Option Bool := none
  move : Int := 0
  rewindSum : Bool := false
  emit : Option Bool := none
  deriving Inhabited

def sample₀ := 20000
def sample₁ := sample₀ + 192*257
def secretOut := sample₁ + 192*257
def entryOut := secretOut + 257*9
def multRead := entryOut + 257*76
def sumRead := multRead + 257*511
def sumOut := sumRead + 257*511
def noise := sumOut + 257*9
def rowRead := noise + 6
def rowWrite := rowRead + 3*511
def bodyRead := rowWrite + 257*9
def bodyOut := bodyRead + 511
def states := bodyOut + 257*19

def framedBit (v i : Nat) (levels : Nat) : Bool :=
  let stride := 2^levels
  if i < v.size*stride then
    i%stride != stride-1 || v.testBit (i/stride)
  else i - v.size*stride < stride/2-1

def act (n m pc : Nat) (inp s acc rows : Option Bool) (coin : Bool) : Act := Id.run do
  -- Initialize and rewind the two bounded arrays independently.
  if pc < 9*n then return ⟨pc+1,0,some false,1,false,none⟩
  if pc == 9*n then return ⟨15500,0,none,-1,false,none⟩
  if pc == 15500 then
    return if s.isSome then ⟨pc,0,none,-1,false,none⟩ else ⟨15501,0,none,1,false,none⟩
  if pc == 15501 then return {next := 5000}
  if 5000 <= pc && pc < 5000+10*m then
    let j := pc-5000
    return ⟨pc+1,2,some (j==10*(m-1)),1,false,none⟩
  if pc == 5000+10*m then return ⟨16000,2,none,-1,false,none⟩
  if pc == 16000 then
    return if rows.isSome then ⟨pc,2,none,-1,false,none⟩ else ⟨16001,2,none,1,false,none⟩
  if pc == 16001 then
    return if s.isSome then {next := sample₀} else ⟨16002,0,none,-1,false,none⟩
  if pc == 16002 then
    return if s.isSome then ⟨pc,0,none,-1,false,none⟩ else ⟨16003,0,none,1,false,none⟩
  if pc == 16003 then
    return if s.isSome then {next := sample₁} else {next := noise,emit := some true}
  if pc == 16004 then
    return if rows.isSome then ⟨16002,0,none,-1,false,none⟩
           else ⟨16005,2,none,-1,false,some false⟩
  if pc == 16005 then
    return if rows.isSome then ⟨pc,2,none,-1,false,none⟩ else ⟨16006,2,none,1,false,none⟩
  if pc == 16006 then
    return if rows.isSome then ⟨bodyRead,2,none,1,false,none⟩ else {}
  if sample₀ <= pc && pc < secretOut then
    let base := if pc < sample₁ then sample₀ else sample₁
    let i := pc-base
    let v := (2*(i%257)+coin.toNat)%257
    let last := if base==sample₀ then secretOut+9*v else entryOut+76*v
    return {next := if i/257==191 then last else base+257*(i/257+1)+v}
  if secretOut <= pc && pc < entryOut then
    let i := pc-secretOut
    return ⟨if i%9==8 then 16001 else pc+1,0,some ((i/9).testBit (8-i%9)),1,false,none⟩
  if entryOut <= pc && pc < multRead then
    let i := pc-entryOut
    let v := i/76
    let j := i%76
    return {next := if j+1==8*v.size+4 then multRead+511*v else pc+1,
            emit := some (framedBit v j 3)}
  if multRead <= pc && pc < sumOut then
    let first := pc < sumRead
    let base := if first then multRead else sumRead
    let i := pc-base
    let v := i/511
    let pref := i%511+1
    let w := 2*pref+((if first then s else acc).getD false).toNat
    if w < 512 then return ⟨base+511*v+w-1,if first then 0 else 1,none,1,false,none⟩
    let out := if first then sumRead+511*((v*(w-512))%257) else sumOut+9*((v+w-512)%257)
    return ⟨out,if first then 0 else 1,none,if first then 1 else 0,false,none⟩
  if sumOut <= pc && pc < noise then
    let i := pc-sumOut
    return ⟨if i%9==8 then 16003 else pc+1,1,some ((i/9).testBit (i%9)),
            if i%9==8 then 0 else -1,false,none⟩
  if pc == noise then return {next := noise+1+coin.toNat,emit := some false}
  if pc==noise+1 || pc==noise+2 then
    return {next := rowRead+511*(pc-noise-1+1-coin.toNat)}
  if rowRead <= pc && pc < rowWrite then
    let i := pc-rowRead
    let w := 2*(i%511+1)+(acc.getD false).toNat
    if w < 512 then return ⟨rowRead+511*(i/511)+w-1,1,some false,1,false,none⟩
    let v := (w-512+i/511+256+(if rows==some true && inp==some true then 128 else 0))%257
    return ⟨rowWrite+9*v,1,some false,0,false,none⟩
  if rowWrite <= pc && pc < bodyRead then
    let i := pc-rowWrite
    -- The final row-read transition has advanced the response head past the slot flag.
    return ⟨if i%9==8 then 16004 else pc+1,2,some ((i/9).testBit (8-i%9)),1,
            i%9<8,none⟩
  if bodyRead <= pc && pc < bodyOut then
    let w := 2*(pc-bodyRead+1)+(rows.getD false).toNat
    return ⟨if w<512 then bodyRead+w-1 else bodyOut+19*(w-512),2,none,1,false,none⟩
  if pc >= bodyOut then
    let i := pc-bodyOut
    return {next := if i%19+1==2*(i/19).size+1 then 16006 else pc+1,
            emit := some (framedBit (i/19) (i%19) 1)}
  return {}

def dir (x : Int) : SignType := if x<0 then -1 else if x>0 then 1 else 0

def issuer (n m : Nat) : Machine where
  tapes := 3
  states := states
  time := 180000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q i w _ coin ↦
      let a := act n m q.val i (w 0) (w 1) (w 2) coin
      let skipFlag := rowRead<=q.val && q.val<rowWrite && a.next>=rowWrite && a.next<bodyRead
      .step {inputTape := 0
             workTapes := fun j ↦
               if j.val==a.tape then (a.write.map some,dir a.move)
               else if j.val==2 && skipFlag then (none,1)
               else if j.val==1 && a.rewindSum then (none,-1)
               else (none,0)
             output := a.emit
             state := if h : a.next < states then some ⟨a.next,h⟩ else none}
            (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) }

end CompactRowIssuer
namespace CompactRowDecoder
open SigabaNeo

structure Act where
  next : Nat := 1000000
  consume : Bool := false
  tape : Nat := 2
  write : Option Bool := none
  move : Int := 0
  out : Option Bool := none
  deriving Inhabited

def skipRow := 5000
def digit := 15000
def secret := digit + 1023*8
def acc := secret + 257*511
def store := acc + 257*511
def endMat := store + 257*9
def skipBody := endMat+1
def body := skipBody + 2*1025
def finish := body + 2*1023
def states := finish + 257*511

def decAct (n m pc : Nat) (inp x y : Option Bool) : Act := Id.run do
  let bit := (inp.getD false).toNat
  if pc < 9*n then return ⟨pc+1,true,0,some (inp.getD false),1,none⟩
  if pc == 9*n then return ⟨4900,false,0,none,-1,none⟩
  if pc == 4900 then
    return if x.isSome then ⟨pc,false,0,none,-1,none⟩ else
      ⟨if m==1 then digit else skipRow,false,0,none,1,none⟩
  if skipRow<=pc && pc<digit then
    let i := pc-skipRow
    let j := i%8
    let base := pc-j
    let nxt := if j==1 && bit==0 then (if i/8+2==m then digit else base+8)
               else if j==3 && bit==0 || j==7 then base else pc+1
    return {next := nxt,consume := true}
  if digit<=pc && pc<secret then
    let tree := (pc-digit)/8+1
    let j := (pc-digit)%8
    let pow := 2^(tree.size-1)
    let v := tree-pow
    if j==1 && bit==0 then return {next := endMat,consume := true}
    if j==3 && bit==0 then
      return {next := if v<257 then secret+v*511 else 1000000,consume := true}
    if j==7 then
      let newTree := 2*pow+v+pow*bit
      return {next := if newTree<1024 then digit+8*(newTree-1) else 1000000,consume := true}
    return {next := pc+1,consume := true}
  if secret<=pc && pc<store then
    let first := pc<acc
    let base := if first then secret else acc
    let i := pc-base
    let w := 2*(i%511+1)+((if first then x else y).getD false).toNat
    if w<512 then return ⟨base+511*(i/511)+w-1,false,if first then 0 else 1,none,1,none⟩
    let nxt := if first then acc+511*((i/511*(w-512))%257)
               else store+9*((i/511+w-512)%257)
    return ⟨nxt,false,if first then 0 else 1,none,if first then 1 else 0,none⟩
  if store<=pc && pc<endMat then
    let i := pc-store
    return ⟨if i%9==8 then digit else pc+1,false,1,some ((i/9).testBit (i%9)),
            if i%9==8 then 0 else -1,none⟩
  if pc==endMat then return {next := if m==1 then body else skipBody,consume := true}
  if skipBody<=pc && pc<body then
    let i := pc-skipBody
    return {next := if i%2==1 then pc-1 else if bit==1 then pc+1
                    else if i/2+2==m then body else pc+2,consume := true}
  if body<=pc && pc<finish then
    let i := pc-body
    let tree := i/2+1
    let pow := 2^(tree.size-1)
    let v := tree-pow
    if i%2==0 then
      return {next := if bit==1 then pc+1 else if v<257 then finish+511*v else 1000000,
              consume := true}
    let newTree := 2*pow+v+pow*bit
    return {next := if newTree<1024 then body+2*(newTree-1) else 1000000,consume := true}
  if finish<=pc then
    let i := pc-finish
    let w := 2*(i%511+1)+(y.getD false).toNat
    if w<512 then return ⟨finish+511*(i/511)+w-1,false,1,none,1,none⟩
    let residual := (i/511+257-(w-512))%257
    return {out := some (64<=residual && residual<=192)}
  return {}

-- Input is the internally recovered raw 9-bit big-endian secret, then the native sample.
def decoder (n m : Nat) : Machine where
  tapes := 2
  states := states
  time := 45000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q inp ws _ _ ↦
      let a := decAct n m q.val inp (ws 0) (ws 1)
      .step { inputTape := if a.consume then 1 else 0
              workTapes := fun j ↦ if j.val==a.tape then
                (a.write.map some,if a.move<0 then -1 else if a.move>0 then 1 else 0) else (none,0)
              output := a.out
              state := if h : a.next<states then some ⟨a.next,h⟩ else none}
            (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) }

end CompactRowDecoder
end Original201
namespace Packed201
namespace CompactRowIssuer
open SigabaNeo

-- Tape 0 holds fixed-width secret residues, tape 1 the running sum, and tape 2 the row bodies.
structure Act where
  next : Nat := 1000000
  tape : Nat := 3
  write : Option Bool := none
  move : Int := 0
  rewindSum : Bool := false
  emit : Option Bool := none
  deriving Inhabited

def sample₀ := 20000
def sample₁ := sample₀ + 192*257
def secretOut := sample₁ + 192*257
def entryOut := secretOut + 257*9
def multRead := entryOut + 257*76
def sumRead := multRead + 257*511
def sumOut := sumRead + 257*9
def noise := sumOut + 257*9
def rowRead := noise + 6
def rowWrite := rowRead + 3*511
def bodyRead := rowWrite + 257*9
def bodyOut := bodyRead + 511
def states := bodyOut + 257*19

def framedBit (v i : Nat) (levels : Nat) : Bool :=
  let stride := 2^levels
  if i < v.size*stride then
    i%stride != stride-1 || v.testBit (i/stride)
  else i - v.size*stride < stride/2-1

def act (n m pc : Nat) (inp s acc rows : Option Bool) (coin : Bool) : Act := Id.run do
  -- Initialize and rewind the two bounded arrays independently.
  if pc < 9*n then return ⟨pc+1,0,some false,1,false,none⟩
  if pc == 9*n then return ⟨15500,0,none,-1,false,none⟩
  if pc == 15500 then
    return if s.isSome then ⟨pc,0,none,-1,false,none⟩ else ⟨15501,0,none,1,false,none⟩
  if pc == 15501 then return {next := 5000}
  if 5000 <= pc && pc < 5000+10*m then
    let j := pc-5000
    return ⟨pc+1,2,some (j==10*(m-1)),1,false,none⟩
  if pc == 5000+10*m then return ⟨16000,2,none,-1,false,none⟩
  if pc == 16000 then
    return if rows.isSome then ⟨pc,2,none,-1,false,none⟩ else ⟨16001,2,none,1,false,none⟩
  if pc == 16001 then
    return if s.isSome then {next := sample₀} else ⟨16002,0,none,-1,false,none⟩
  if pc == 16002 then
    return if s.isSome then ⟨pc,0,none,-1,false,none⟩ else ⟨16003,0,none,1,false,none⟩
  if pc == 16003 then
    return if s.isSome then {next := sample₁} else {next := noise,emit := some true}
  if pc == 16004 then
    return if rows.isSome then ⟨16002,0,none,-1,false,none⟩
           else ⟨16005,2,none,-1,false,some false⟩
  if pc == 16005 then
    return if rows.isSome then ⟨pc,2,none,-1,false,none⟩ else ⟨16006,2,none,1,false,none⟩
  if pc == 16006 then
    return if rows.isSome then ⟨bodyRead,2,none,1,false,none⟩ else {}
  if sample₀ <= pc && pc < secretOut then
    let base := if pc < sample₁ then sample₀ else sample₁
    let i := pc-base
    let v := (2*(i%257)+coin.toNat)%257
    let last := if base==sample₀ then secretOut+9*v else entryOut+76*v
    return {next := if i/257==191 then last else base+257*(i/257+1)+v}
  if secretOut <= pc && pc < entryOut then
    let i := pc-secretOut
    return ⟨if i%9==8 then 16001 else pc+1,0,some ((i/9).testBit (8-i%9)),1,false,none⟩
  if entryOut <= pc && pc < multRead then
    let i := pc-entryOut
    let v := i/76
    let j := i%76
    return {next := if j+1==8*v.size+4 then multRead+511*v else pc+1,
            emit := some (framedBit v j 3)}
  if multRead <= pc && pc < sumRead then
    let i := pc-multRead
    let w := 2*(i%511+1)+(s.getD false).toNat
    if w < 512 then return ⟨multRead+511*(i/511)+w-1,0,none,1,false,none⟩
    return ⟨sumRead+((i/511)*(w-512))%257,0,none,1,false,none⟩
  if sumRead <= pc && pc < sumOut then
    let i := pc-sumRead
    let depth := i/257
    let v := (i%257+(acc.getD false).toNat*2^(8-depth))%257
    if depth<8 then return ⟨sumRead+257*(depth+1)+v,1,none,1,false,none⟩
    return ⟨sumOut+9*v,1,none,0,false,none⟩
  if sumOut <= pc && pc < noise then
    let i := pc-sumOut
    return ⟨if i%9==8 then 16003 else pc+1,1,some ((i/9).testBit (i%9)),
            if i%9==8 then 0 else -1,false,none⟩
  if pc == noise then return {next := noise+1+coin.toNat,emit := some false}
  if pc==noise+1 || pc==noise+2 then
    return {next := rowRead+511*(pc-noise-1+1-coin.toNat)}
  if rowRead <= pc && pc < rowWrite then
    let i := pc-rowRead
    let w := 2*(i%511+1)+(acc.getD false).toNat
    if w < 512 then return ⟨rowRead+511*(i/511)+w-1,1,some false,1,false,none⟩
    let v := (w-512+i/511+256+(if rows==some true && inp==some true then 128 else 0))%257
    return ⟨rowWrite+9*v,1,some false,0,false,none⟩
  if rowWrite <= pc && pc < bodyRead then
    let i := pc-rowWrite
    -- The final row-read transition has advanced the response head past the slot flag.
    return ⟨if i%9==8 then 16004 else pc+1,2,some ((i/9).testBit (8-i%9)),1,
            i%9<8,none⟩
  if bodyRead <= pc && pc < bodyOut then
    let w := 2*(pc-bodyRead+1)+(rows.getD false).toNat
    return ⟨if w<512 then bodyRead+w-1 else bodyOut+19*(w-512),2,none,1,false,none⟩
  if pc >= bodyOut then
    let i := pc-bodyOut
    return {next := if i%19+1==2*(i/19).size+1 then 16006 else pc+1,
            emit := some (framedBit (i/19) (i%19) 1)}
  return {}

def dir (x : Int) : SignType := if x<0 then -1 else if x>0 then 1 else 0

def issuer (n m : Nat) : Machine where
  tapes := 3
  states := states
  time := 180000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q i w _ coin ↦
      let a := act n m q.val i (w 0) (w 1) (w 2) coin
      let skipFlag := rowRead<=q.val && q.val<rowWrite && a.next>=rowWrite && a.next<bodyRead
      .step {inputTape := 0
             workTapes := fun j ↦
               if j.val==a.tape then (a.write.map some,dir a.move)
               else if j.val==2 && skipFlag then (none,1)
               else if j.val==1 && a.rewindSum then (none,-1)
               else (none,0)
             output := a.emit
             state := if h : a.next < states then some ⟨a.next,h⟩ else none}
            (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) }

end CompactRowIssuer
namespace CompactRowDecoder
open SigabaNeo

structure Act where
  next : Nat := 1000000
  consume : Bool := false
  tape : Nat := 2
  write : Option Bool := none
  move : Int := 0
  out : Option Bool := none
  deriving Inhabited

def skipRow := 5000
def digit := 15000
def secret := digit + 1023*8
def acc := secret + 257*511
def store := acc + 257*9
def endMat := store + 257*9
def skipBody := endMat+1
def body := skipBody + 2*1025
def finish := body + 2*1023
def states := finish + 257*9

def decAct (n m pc : Nat) (inp x y : Option Bool) : Act := Id.run do
  let bit := (inp.getD false).toNat
  if pc < 9*n then return ⟨pc+1,true,0,some (inp.getD false),1,none⟩
  if pc == 9*n then return ⟨4900,false,0,none,-1,none⟩
  if pc == 4900 then
    return if x.isSome then ⟨pc,false,0,none,-1,none⟩ else
      ⟨if m==1 then digit else skipRow,false,0,none,1,none⟩
  if skipRow<=pc && pc<digit then
    let i := pc-skipRow
    let j := i%8
    let base := pc-j
    let nxt := if j==1 && bit==0 then (if i/8+2==m then digit else base+8)
               else if j==3 && bit==0 || j==7 then base else pc+1
    return {next := nxt,consume := true}
  if digit<=pc && pc<secret then
    let tree := (pc-digit)/8+1
    let j := (pc-digit)%8
    let pow := 2^(tree.size-1)
    let v := tree-pow
    if j==1 && bit==0 then return {next := endMat,consume := true}
    if j==3 && bit==0 then
      return {next := if v<257 then secret+v*511 else 1000000,consume := true}
    if j==7 then
      let newTree := 2*pow+v+pow*bit
      return {next := if newTree<1024 then digit+8*(newTree-1) else 1000000,consume := true}
    return {next := pc+1,consume := true}
  if secret<=pc && pc<acc then
    let i := pc-secret
    let w := 2*(i%511+1)+(x.getD false).toNat
    if w<512 then return ⟨secret+511*(i/511)+w-1,false,0,none,1,none⟩
    return ⟨acc+((i/511)*(w-512))%257,false,0,none,1,none⟩
  if acc<=pc && pc<store then
    let i := pc-acc
    let depth := i/257
    let v := (i%257+(y.getD false).toNat*2^(8-depth))%257
    if depth<8 then return ⟨acc+257*(depth+1)+v,false,1,none,1,none⟩
    return ⟨store+9*v,false,1,none,0,none⟩
  if store<=pc && pc<endMat then
    let i := pc-store
    return ⟨if i%9==8 then digit else pc+1,false,1,some ((i/9).testBit (i%9)),
            if i%9==8 then 0 else -1,none⟩
  if pc==endMat then return {next := if m==1 then body else skipBody,consume := true}
  if skipBody<=pc && pc<body then
    let i := pc-skipBody
    return {next := if i%2==1 then pc-1 else if bit==1 then pc+1
                    else if i/2+2==m then body else pc+2,consume := true}
  if body<=pc && pc<finish then
    let i := pc-body
    let tree := i/2+1
    let pow := 2^(tree.size-1)
    let v := tree-pow
    if i%2==0 then
      return {next := if bit==1 then pc+1 else if v<257 then finish+v else 1000000,
              consume := true}
    let newTree := 2*pow+v+pow*bit
    return {next := if newTree<1024 then body+2*(newTree-1) else 1000000,consume := true}
  if finish<=pc then
    let i := pc-finish
    let depth := i/257
    let residual := (i%257+257-(y.getD false).toNat*2^(8-depth))%257
    if depth<8 then return ⟨finish+257*(depth+1)+residual,false,1,none,1,none⟩
    return {out := some (64<=residual && residual<=192)}
  return {}

-- Input is the internally recovered raw 9-bit big-endian secret, then the native sample.
def decoder (n m : Nat) : Machine where
  tapes := 2
  states := states
  time := 45000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q inp ws _ _ ↦
      let a := decAct n m q.val inp (ws 0) (ws 1)
      .step { inputTape := if a.consume then 1 else 0
              workTapes := fun j ↦ if j.val==a.tape then
                (a.write.map some,if a.move<0 then -1 else if a.move>0 then 1 else 0) else (none,0)
              output := a.out
              state := if h : a.next<states then some ⟨a.next,h⟩ else none}
            (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) }

end CompactRowDecoder
end Packed201

namespace CompactTerminal201
theorem original_cost : (Original201.CompactRowIssuer.issuer 512 1025).cost + (Original201.CompactRowDecoder.decoder 512 1025).cost = 3285674370 := by decide
theorem packed_cost : (Packed201.CompactRowIssuer.issuer 512 1025).cost + (Packed201.CompactRowDecoder.decoder 512 1025).cost = 2113286580 := by decide
end CompactTerminal201
