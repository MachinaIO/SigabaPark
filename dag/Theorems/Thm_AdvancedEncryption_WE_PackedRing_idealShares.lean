import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.idealShares {A S : Type*} [Fintype A] [Nonempty A]
    (e : A ≃ A) (shares : A→S) (mask : A→Bool)
    (hs : ∀ a,shares (e a)=shares a) (hm : ∀ a,mask (e a)= !mask a) :
    (PMF.uniformOfFintype A).map (fun a => (shares a,mask a)) =
    (PMF.uniformOfFintype A).map (fun a => (shares a,!mask a)) := by sorry
