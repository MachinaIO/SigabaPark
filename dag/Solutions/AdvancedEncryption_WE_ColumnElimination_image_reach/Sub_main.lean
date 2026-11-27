import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem solution {K V U : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] (P : V →ₗ[K] U) (cs : List V) (z : U) :
    Reach K (cs.map P) z ↔ ∃ v, Reach K cs v ∧ P v = z := by
  induction cs generalizing z with
  | nil => simp [Reach, eq_comm]
  | cons a cs ih =>
    simp only [List.map_cons, Reach]
    constructor
    · rintro ⟨t,u,hu,rfl⟩
      obtain ⟨v,hv,rfl⟩ := (ih u).mp hu
      exact ⟨t • a + v, ⟨t,v,hv,rfl⟩, by simp⟩
    · rintro ⟨_,⟨t,v,hv,rfl⟩,rfl⟩
      exact ⟨t,P v,(ih _).mpr ⟨_,hv,rfl⟩,by simp⟩
