import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution (p : ℕ) [NeZero p] [NeZero (2*p)] :
    (PMF.uniformOfFintype (Fin (2*p))).map (RingPacket.splitDigit p) =
    PMF.uniformOfFintype (Fin 2 × Fin p) := PMF.uniformOfFintype_map_equiv _
