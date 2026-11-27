import Mathlib

open scoped BigOperators

theorem solution {I G : Type} [DecidableEq I] [AddCommGroup G]
    (O : AddSubgroup G) (c : Finset I → G) (s : Finset I)
    (hproper : ∀ t, t ⊂ s → c t ∈ O) :
    (∑ t ∈ s.powerset, c t) ∈ O ↔ c s ∈ O := by
  classical
  have hs : s ∈ s.powerset := Finset.mem_powerset.mpr (by rfl)
  have rest : (∑ t ∈ s.powerset.erase s, c t) ∈ O := by
    apply O.sum_mem
    intro t ht
    have h := Finset.mem_erase.mp ht
    exact hproper t (lt_of_le_of_ne (Finset.mem_powerset.mp h.2) h.1)
  rw [← Finset.sum_erase_add _ _ hs]
  constructor
  · intro h
    have hh := O.sub_mem h rest
    simpa only [add_sub_cancel_left] using hh
  · exact fun h => O.add_mem rest h
