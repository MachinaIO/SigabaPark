import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem solution {I J : Type} (key : J→I) (p : J→ℤ) (q : ℤ) :
    (∃ s : I→ℤ, ∀ j, eqm q (p j) (s (key j))) ↔
      ∀ j k, key j=key k → eqm q (p j) (p k) := by
  classical
  constructor
  · rintro ⟨s,hs⟩ j k hk
    obtain ⟨u,hu⟩ := hs j
    obtain ⟨v,hv⟩ := hs k
    rw [hk] at hu
    exact ⟨u-v, by linear_combination hu-hv⟩
  · intro H
    let s := fun i => if h : ∃ j,key j=i then p h.choose else 1
    refine ⟨s,fun j => ?_⟩
    dsimp [s]
    rw [dite_eq_left (show ∃ k,key k=key j from ⟨j,rfl⟩)]
    apply H
    exact (Classical.choose_spec (show ∃ k,key k=key j from ⟨j,rfl⟩)).symm
