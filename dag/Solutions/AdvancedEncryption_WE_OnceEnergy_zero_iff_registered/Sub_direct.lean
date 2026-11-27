import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceTrace SigabaNeo
/-- A zero-energy trace exists on a given assignment exactly when the registered gate evaluator accepts. -/
theorem solution (w : List Bool) (gs : GateList) :
    (∃ rows : List ((ℕ × ℕ) × Bool), rows.map Prod.fst = gs ∧
      energy (true::w,true) rows = 0) ↔ evalGates (w,gs) = true := by
  have pen0 (x y z : Bool) : pen x y z = 0 ↔ z = !(x && y) := by
    cases x <;> cases y <;> cases z <;> decide
  have aux (gates : GateList) (s : List Bool × Bool) :
      (∃ rows : List ((ℕ × ℕ) × Bool), rows.map Prod.fst = gates ∧ energy s rows = 0) ↔
      (gates.foldl estep s).2 = true := by
    induction gates generalizing s with
    | nil =>
      simp [energy]
    | cons g gs ih =>
      obtain ⟨i,j⟩ := g
      constructor
      · rintro ⟨rows,h,e⟩
        cases rows with
        | nil => simp at h
        | cons p rows =>
          obtain ⟨⟨a,b⟩,z⟩ := p
          simp at h
          obtain ⟨⟨rfl,rfl⟩,ht⟩ := h
          change pen (s.1.getD a true) (s.1.getD b true) z + energy (s.1 ++ [z],z) rows = 0 at e
          have hz := (pen0 _ _ z).mp (Nat.eq_zero_of_add_eq_zero_right e)
          subst z
          apply (ih (estep s (a,b))).mp
          exact ⟨rows,ht,Nat.eq_zero_of_add_eq_zero_left e⟩
      · intro h
        obtain ⟨rows,ht,he⟩ := (ih (estep s (i,j))).mpr h
        let z := !(s.1.getD i true && s.1.getD j true)
        refine ⟨((i,j),z)::rows,by simp [ht],?_⟩
        change pen (s.1.getD i true) (s.1.getD j true) z + _ = 0
        rw [(pen0 _ _ z).mpr rfl,zero_add]
        exact he
  exact aux gs (true::w,true)
