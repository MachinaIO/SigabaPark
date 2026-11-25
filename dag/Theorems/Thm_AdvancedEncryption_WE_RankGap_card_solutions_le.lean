import Mathlib
open Matrix

theorem AdvancedEncryption.WE.RankGap.card_solutions_le {K : Type*} [Field K] [DecidableEq K]
    {m n : ℕ} (N : Matrix (Fin m) (Fin n) K) (T : Finset K) (α : Fin m → K) :
    ((Finset.univ : Finset (Fin n → T)).filter
        (fun r => N *ᵥ (fun i => (r i : K)) = α)).card ≤ T.card ^ (n - N.rank) := by sorry
