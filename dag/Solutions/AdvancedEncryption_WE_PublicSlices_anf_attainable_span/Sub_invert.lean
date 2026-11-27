import Mathlib

theorem solution {K V X : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Finset X → V) (W : Submodule K V) :
    (∀ s : Finset X, (∑ t ∈ s.powerset, f t) ∈ W) ↔ (∀ t, f t ∈ W) := by
  classical
  constructor
  · intro he s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      have hrest : (∑ t ∈ s.powerset.erase s, f t) ∈ W := by
        apply W.sum_mem
        intro t ht
        obtain ⟨hne,hts⟩ := Finset.mem_erase.mp ht
        exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hts, hne⟩)
      have hfull := he s
      rw [← Finset.sum_erase_add s.powerset f (Finset.mem_powerset_self s)] at hfull
      simpa using W.sub_mem hfull hrest
  · intro hf s
    exact W.sum_mem (fun t _ => hf t)
