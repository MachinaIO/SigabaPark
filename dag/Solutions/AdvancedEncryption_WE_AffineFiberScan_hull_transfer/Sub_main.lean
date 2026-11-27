import Definitions.Def_AffineFiberScan

open AdvancedEncryption.WE.AffineFiberScan

theorem solution {W : Type} (hull : (W → Prop) → (W → Prop) → W → Prop)
    (union_le : ∀ f g w, f w ∨ g w → hull f g w)
    (a b : Bool → W → Prop) (x y : Bool) (w : W) (ha : a x w) (hb : b y w) :
    nandFiber hull a b (!(x && y)) w := by
  cases x <;> cases y
  · exact union_le _ _ _ (Or.inl ha)
  · exact union_le _ _ _ (Or.inl ha)
  · exact union_le _ _ _ (Or.inr hb)
  · exact ⟨ha, hb⟩
