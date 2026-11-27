import Mathlib

theorem AdvancedEncryption.WE.PublicTail.dictionary_criterion {R X U Y Z : Type} (parse : R → Option U)
    (cover : ∀ u, ∃ raw, parse raw = some u) (fallback : X → U → Y × Z)
    (privatePart : X → Y) (dictionary : U → Z) :
    (∀ x raw, (parse raw).map (fallback x) =
      (parse raw).map (fun u ↦ (privatePart x, dictionary u))) ↔
    ∀ x u, fallback x u = (privatePart x, dictionary u) := by sorry
