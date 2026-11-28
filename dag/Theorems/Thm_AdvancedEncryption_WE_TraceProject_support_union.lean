import Mathlib

theorem AdvancedEncryption.WE.TraceProject.support_union {I V : Type} [Fintype I] [DecidableEq V]
    (F : I → Finset V → Prop) (old : Finset V) (cert : I → Finset V)
    (mono : ∀ i, Monotone (F i)) (sub : ∀ i, cert i ⊆ old)
    (keep : ∀ i, F i old → F i (cert i)) :
    let small := Finset.univ.biUnion cert
    small ⊆ old ∧ small.card ≤ ∑ i, (cert i).card ∧ ∀ i, F i small ↔ F i old := by
  sorry
