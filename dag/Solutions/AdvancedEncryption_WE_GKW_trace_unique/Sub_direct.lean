import Definitions.Def_WE_GKW_Trace

open SigabaNeo AdvancedEncryption.WE.GKW

theorem solution (w : List Bool) (gs : GateList) (b : Bool) :
    ∃ t, TraceFits w gs t ∧ gs.foldl estep (w, b) = (w ++ t, t.getLastD b) ∧
      ∀ u, TraceFits w gs u → u = t := by
  induction gs generalizing w b with
  | nil =>
    refine ⟨[], trivial, by simp, ?_⟩
    intro u hu
    cases u with
    | nil => rfl
    | cons => exact False.elim hu
  | cons g gs ih =>
    let v := !(w.getD g.1 true && w.getD g.2 true)
    obtain ⟨t, ht, heval, hu⟩ := ih (w ++ [v]) v
    refine ⟨v :: t, ⟨rfl, ht⟩, ?_, ?_⟩
    · rw [List.foldl_cons]
      change gs.foldl estep (w ++ [v], v) = _
      rw [heval]
      cases t <;> simp [List.getLastD]
    · intro u hok
      cases u with
      | nil => exact False.elim hok
      | cons a as =>
        obtain ⟨ha, has⟩ := hok
        change a = v at ha
        subst a
        rw [hu as has]
