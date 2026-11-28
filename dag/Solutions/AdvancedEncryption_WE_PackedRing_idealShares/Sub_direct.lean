import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution {A S : Type*} [Fintype A] [Nonempty A]
    (e : A ≃ A) (shares : A→S) (mask : A→Bool)
    (hs : ∀ a,shares (e a)=shares a) (hm : ∀ a,mask (e a)= !mask a) :
    (PMF.uniformOfFintype A).map (fun a => (shares a,mask a)) =
    (PMF.uniformOfFintype A).map (fun a => (shares a,!mask a)) := by
  calc _ = ((PMF.uniformOfFintype A).map e).map (fun a => (shares a,mask a)) := by
             rw [PMF.uniformOfFintype_map_equiv]
       _ = _ := by rw [PMF.map_comp]; congr 1; funext a; simp [Function.comp,hs,hm]
