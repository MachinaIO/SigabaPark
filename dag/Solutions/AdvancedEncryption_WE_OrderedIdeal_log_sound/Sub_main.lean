import Definitions.Def_OrderedNand

open OrderedNand

theorem solution {I W : Type} {base : W → Tags I → Prop} {edges : W → W → W → Prop}
    (val : (I → Bool) → W → Prop)
    (initial : ∀ w S x, base w S → extendsT x S → val x w)
    (step : ∀ a b c x, edges a b c → val x a → val x b → val x c)
    {w S} (d : Derives base edges w S) : ∀ x, extendsT x S → val x w := by
  induction d with
  | initial h => intro x hx; exact initial _ _ x h hx
  | gate p q h ihp ihq =>
    intro x hx
    exact step _ _ _ x h (ihp x (fun i b hi => hx i b (Or.inl hi)))
      (ihq x (fun i b hi => hx i b (Or.inr hi)))
  | extra p h ih =>
    intro x hx
    exact ih x (fun i b hi => hx i b (h hi))
