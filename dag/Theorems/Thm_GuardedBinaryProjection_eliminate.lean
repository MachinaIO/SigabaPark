import Definitions.Def_GuardedBinaryProjection
import Mathlib.Tactic

theorem GuardedBinaryProjection.eliminate {A I J : Type*} (base future : A → Prop) (P : I → A → Prop) (N : J → A → Prop) :
    (∃ v x, future v ∧ GuardedBinaryProjection.bucket base P N v x) ↔
    ∃ v, future v ∧ GuardedBinaryProjection.reduced base P N v := by
  sorry
