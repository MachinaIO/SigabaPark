import Definitions.Def_AffineFiberScan

open AdvancedEncryption.WE.AffineFiberScan

theorem AdvancedEncryption.WE.AffineFiberScan.hull_transfer {W : Type} (hull : (W → Prop) → (W → Prop) → W → Prop)
    (union_le : ∀ f g w, f w ∨ g w → hull f g w)
    (a b : Bool → W → Prop) (x y : Bool) (w : W) (ha : a x w) (hb : b y w) :
    nandFiber hull a b (!(x && y)) w := by sorry
