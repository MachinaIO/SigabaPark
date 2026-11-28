import Definitions.Def_DensityTrials

open AdvancedEncryption.WE.DensityTrials

theorem solution {I : Type} (inputs : List (I → Bool)) (gs : SigabaNeo.GateList) (i : I) :
    (gs.foldl batchStep ((fun _ => true) :: inputs, fun _ => true)).2 i =
      SigabaNeo.evalGates (inputs.map (fun c => c i), gs) := by
  have get : ∀ (xs : List (I → Bool)) (k : Nat),
      (xs.getD k (fun _ => true)) i = (xs.map (fun c => c i)).getD k true := by
    intro xs
    induction xs with
    | nil => intro k; cases k <;> rfl
    | cons a xs ih => intro k; cases k with | zero => rfl | succ k => exact ih k
  have go : ∀ (gs : SigabaNeo.GateList) (xs : List (I → Bool)) (last : I → Bool),
      (gs.foldl batchStep (xs,last)).2 i =
        (gs.foldl SigabaNeo.estep (xs.map (fun c => c i),last i)).2 := by
    intro gates
    induction gates with
    | nil => intro xs last; rfl
    | cons g gates ih =>
      intro xs last
      simp only [List.foldl_cons, batchStep, SigabaNeo.estep]
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil, get]
  exact go gs _ _
