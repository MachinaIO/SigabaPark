import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem solution (U V : Finset (Finset (Fin 128)))
    (h : (Finset.univ.erase (∅ : Finset (Fin 128))) ⊆ U ∪ V) :
    2^127 ≤ U.card ∨ 2^127 ≤ V.card := by
  have hc := (Finset.card_le_card h).trans (Finset.card_union_le U V)
  have hz : (Finset.univ.erase (∅ : Finset (Fin 128))).card = 2^128-1 := by simp
  rw [hz] at hc
  omega
