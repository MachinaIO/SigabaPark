import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (a : V) (l : V →ₗ[K] K) (hl : a = 0 ∨ l a = 1) (cs : List V) (v : V) :
    Reach K (a :: cs) v ↔ Reach K (cs.map (kill a l)) (kill a l v) := by
  have image_reach {K V U : Type} [Field K] [AddCommGroup V] [Module K V]
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
  have zero : kill a l a = 0 := by
    rcases hl with rfl | h <;> simp [kill, *]
  rw [image_reach]
  constructor
  · rintro ⟨t,u,hu,rfl⟩
    exact ⟨u,hu,by simp [zero]⟩
  · rintro ⟨u,hu,eq⟩
    change u - l u • a = v - l v • a at eq
    refine ⟨l v - l u,u,hu,?_⟩
    rw [sub_smul]
    calc
      v = (v - l v • a) + l v • a := by abel
      _ = (u - l u • a) + l v • a := by rw [← eq]
      _ = l v • a - l u • a + u := by abel
