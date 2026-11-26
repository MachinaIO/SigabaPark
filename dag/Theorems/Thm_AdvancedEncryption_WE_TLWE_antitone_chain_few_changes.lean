import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

theorem AdvancedEncryption.WE.TLWE.antitone_chain_few_changes {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U : ℕ → Submodule K V) (hU : Antitone U) (N : ℕ) :
    ((Finset.range N).filter (fun t => U (t + 1) ≠ U t)).card ≤ Module.finrank K V := by sorry
