import Definitions.Def_OrderedNand

open OrderedNand

theorem solution {I : Type} (S : Tags I) (hc : consistent S) : ∃ x, extendsT x S := by
  classical
  refine ⟨fun i => decide ((i,true) ∈ S), ?_⟩
  intro i b hb
  cases b with
  | false => simp [show (i,true) ∉ S from fun ht => hc i ⟨hb,ht⟩]
  | true => simp [hb]
