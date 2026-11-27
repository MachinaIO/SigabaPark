import Definitions.Def_WE_TraceLock

open SigabaNeo AdvancedEncryption.WE.TraceLock


theorem AdvancedEncryption.WE.TraceLock.check_shape (gs : GateList) (hg : gs.length = 4096) (w t : ℕ → Bool) :
    let h := (inputs 128).map (Atom.read w t)
    (predicate gs).depth = 15 ∧ (predicate gs).gates = 12288 ∧
    ((predicate gs).eval w t = true ↔
      segment t 0 4096 = (gs.foldl estep (h,true)).1.drop h.length ∧ t 4095 = true) := by
  sorry
