import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem AdvancedEncryption.WE.FrontierNand.point (U V : Finset (Finset (Fin 128)))
    (h : (Finset.univ.erase (∅ : Finset (Fin 128))) ⊆ U ∪ V) :
    2^127 ≤ U.card ∨ 2^127 ≤ V.card := by sorry
