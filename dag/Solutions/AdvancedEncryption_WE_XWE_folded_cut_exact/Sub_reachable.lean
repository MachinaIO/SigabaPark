import Mathlib.Data.Finset.Union

theorem solution {S : Type} [DecidableEq S] (layers : List (Finset (S → S)))
    (initial : Finset S) (z : S) :
    z ∈ layers.foldl (fun states layer ↦ states.biUnion fun s ↦ layer.image (fun f ↦ f s)) initial ↔
    ∃ s ∈ initial, ∃ path : List (S → S),
      List.Forall₂ (fun f layer ↦ f ∈ layer) path layers ∧
      path.foldl (fun t f ↦ f t) s = z := by
  induction layers generalizing initial with
  | nil =>
    constructor
    · intro h
      exact ⟨z, h, [], .nil, rfl⟩
    · rintro ⟨s, hs, p, hp, he⟩
      cases hp
      simpa [← he] using hs
  | cons l ls ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · rintro ⟨t, ht, p, hp, he⟩
      obtain ⟨s, hs, ht⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨s, hs, f :: p, .cons hf hp, he⟩
    · rintro ⟨s, hs, p, hp, he⟩
      cases hp with
      | cons hf ht =>
        exact ⟨_, Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨_, hf, rfl⟩⟩,
          _, ht, he⟩
