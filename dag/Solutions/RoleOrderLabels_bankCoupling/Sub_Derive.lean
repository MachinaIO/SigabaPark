import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem solution {C G : Type*} [AddCommGroup G] (L R : Set C) (sep : Disjoint L R)
    (b : G) (k : C → G) :
    (∀ c ∈ L, RoleOrderLabels.rekey R b k c = k c) ∧
    (∀ c ∈ R, RoleOrderLabels.rekey R b k c = k c + b) := by
  classical
  constructor
  · intro c hc
    have hn : c ∉ R := fun hh => Set.disjoint_left.mp sep hc hh
    simp [RoleOrderLabels.rekey, hn]
  · intro c hc
    simp [RoleOrderLabels.rekey,hc]
