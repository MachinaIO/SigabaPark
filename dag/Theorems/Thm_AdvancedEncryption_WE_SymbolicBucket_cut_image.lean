import Mathlib.Logic.Function.Basic

theorem AdvancedEncryption.WE.SymbolicBucket.cut_image {P U Z V : Type} (coords : U → Z) (onto : Function.Surjective coords)
    (cut : P → U → V) (expand : P → Z → V) (out : P → V → Bool)
    (cert : ∀ p u, cut p u = expand p (coords u)) (p : P) :
    (∃ u, out p (cut p u) = true) ↔ ∃ z, out p (expand p z) = true := by
  sorry
