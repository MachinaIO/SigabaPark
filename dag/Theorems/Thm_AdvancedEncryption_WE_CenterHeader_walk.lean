import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem AdvancedEncryption.WE.CenterHeader.walk {V W : Type} [AddCommGroup W] (P : V → W) (u : V) (vs : List V) :
    walkSum P u vs = P (vs.getLastD u) - P u := by sorry
