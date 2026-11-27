import Mathlib

theorem solution {R X U Y Z : Type} (parse : R → Option U)
    (cover : ∀ u, ∃ raw, parse raw = some u) (fallback : X → U → Y × Z)
    (privatePart : X → Y) (dictionary : U → Z) :
    (∀ x raw, (parse raw).map (fallback x) =
      (parse raw).map (fun u ↦ (privatePart x, dictionary u))) ↔
    ∀ x u, fallback x u = (privatePart x, dictionary u) := by
  constructor
  · intro h x u
    obtain ⟨raw, hr⟩ := cover u
    simpa [hr] using h x raw
  · intro h x raw
    cases hp : parse raw with
    | none => rfl
    | some u => simpa using h x u
