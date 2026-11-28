import Definitions.Def_GuardedBinaryProjection
import Mathlib.Tactic

theorem solution {A I J : Type*} (base future : A → Prop) (P : I → A → Prop) (N : J → A → Prop) :
    (∃ v x, future v ∧ GuardedBinaryProjection.bucket base P N v x) ↔
    ∃ v, future v ∧ GuardedBinaryProjection.reduced base P N v := by
  classical
  constructor
  · rintro ⟨v,x,hf,hb,hp,hn⟩
    refine ⟨v,hf,hb,fun i j => ?_⟩
    cases x with
    | false => exact Or.inl (by simpa using hp i)
    | true => exact Or.inr (by simpa using hn j)
  · rintro ⟨v,hf,hb,h⟩
    by_cases hp : ∀ i, P i v
    · exact ⟨v,false,hf,hb,fun i => Or.inr (hp i),fun _ => Or.inl rfl⟩
    · push Not at hp
      obtain ⟨i,hi⟩ := hp
      exact ⟨v,true,hf,hb,fun _ => Or.inl rfl,fun j => Or.inr ((h i j).resolve_left hi)⟩
