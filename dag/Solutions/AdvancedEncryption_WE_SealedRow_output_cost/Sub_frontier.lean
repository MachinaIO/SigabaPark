import Definitions.Def_WE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import SigabaNeoStd.Machines.Compose.AndThen

open SigabaNeo AdvancedEncryption

theorem solution (R : WE.Relation) (p : WE.Params) (impl : Impl WE.sig) (φ : R.Stmt)
    (β : Bool) (ct : List Bool) (hs : ct ∈ (WE.enc (R := R) p impl φ β).support) (hn : ct ≠ []) :
    2 * ct.length + 1 ≤ (impl.machine WE.Alg.enc).time := by
  unfold WE.enc Impl.run at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨xs, hxs, rfl⟩ := hs
  rw [PMF.mem_support_map_iff] at hxs
  obtain ⟨w, hw, rfl⟩ := hxs
  change (decodeTuple 1 w).getD 0 [] ≠ [] at hn
  change 2 * ((decodeTuple 1 w).getD 0 []).length + 1 ≤ _
  have valid : ∃ xs : List (List Bool), xs.length = 1 ∧ encodeTuple xs = w := by
    by_contra h
    simp [decodeTuple, h] at hn
  obtain ⟨ys, hy, rfl⟩ := valid
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hy
  rw [show 1 = [z].length from rfl, decodeTuple_encodeTuple]
  rw [Machine.run_eq_law, PMF.mem_support_map_iff] at hw
  obtain ⟨cfg, hc, hword⟩ := hw
  have ht := Compose.length_output_of_mem_law _ _ _ _ hc
  change cfg.tapes.output.length ≤ 0 + _ at ht
  rw [hword] at ht
  simpa [encodeTuple, Turing.MultiTapeTM.length_encList] using ht
