import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem solution (gs : SigabaNeo.GateList) : decodeWirePairs (SigabaNeo.encGates gs) = gs := by
  unfold decodeWirePairs SigabaNeo.encGates
  rw [frames_encList]
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    change ((unframe (frame (List.replicate a true) ++ List.replicate b true)).length,
      (dropFrame (frame (List.replicate a true) ++ List.replicate b true)).length) = (a,b)
    simp [unframe_frame_append, dropFrame_frame_append]
