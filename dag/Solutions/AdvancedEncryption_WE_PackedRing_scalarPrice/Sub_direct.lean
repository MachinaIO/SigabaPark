import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution :
    let n:=1024; let w:=26; let m:=53
    let sampleBits:=m*n*220+n*w+m*n*w
    let S:=sampleBits+m*n*(400*(2*220+2)+401*(w+2))+m*n*n*(8*(w+1)^2)+m*n*1000+w*n*1000+1000
    let states:=16*(2^39)^2
    sampleBits=13377536 ∧ S<2^39 ∧
      18*states*(8+Nat.size states)+8*(2^39)^2<2^93 := by decide
