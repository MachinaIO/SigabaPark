import Definitions.Def_OrderedNand

open OrderedNand

theorem AdvancedEncryption.WE.OrderedIdeal.log_sound {I W : Type} {base : W → Tags I → Prop} {edges : W → W → W → Prop}
    (val : (I → Bool) → W → Prop)
    (initial : ∀ w S x, base w S → extendsT x S → val x w)
    (step : ∀ a b c x, edges a b c → val x a → val x b → val x c)
    {w S} (d : Derives base edges w S) : ∀ x, extendsT x S → val x w := by sorry
