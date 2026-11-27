import Mathlib

theorem solution {I V : Type} [Fintype I] [DecidableEq V]
    (F : I → Finset V → Prop) (old : Finset V) (cert : I → Finset V)
    (mono : ∀ i, Monotone (F i)) (sub : ∀ i, cert i ⊆ old)
    (keep : ∀ i, F i old → F i (cert i)) :
    let small := Finset.univ.biUnion cert
    small ⊆ old ∧ small.card ≤ ∑ i, (cert i).card ∧ ∀ i, F i small ↔ F i old := by
  dsimp only
  have hsub : Finset.univ.biUnion cert ⊆ old := by
    intro v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 hv
    exact sub i hi
  refine ⟨hsub, Finset.card_biUnion_le, ?_⟩
  intro i
  constructor
  · exact mono i hsub
  · intro h
    apply mono i _ (keep i h)
    exact fun v hv ↦ Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩
