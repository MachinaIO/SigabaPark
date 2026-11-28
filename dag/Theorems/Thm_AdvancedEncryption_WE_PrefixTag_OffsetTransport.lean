import Mathlib

theorem AdvancedEncryption.WE.PrefixTag.OffsetTransport (pad edge message : Bool) :
    Bool.xor (Bool.xor pad message) edge = Bool.xor (Bool.xor pad edge) message := by sorry
