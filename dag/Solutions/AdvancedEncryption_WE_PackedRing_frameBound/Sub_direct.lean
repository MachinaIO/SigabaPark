import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution (ct : List Bool) (h : ct.length=RingPacket.bankBits 1024 26 1024) :
    (SigabaNeo.encodeTuple [ct]).length>2^32 := by
  rw [SigabaNeo.Tape.Prog.encodeTuple_single,SigabaNeo.Tape.Prog.length_frame,h]
  decide
