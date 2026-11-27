import Mathlib.LinearAlgebra.Matrix.Rank

theorem AdvancedEncryption.WE.Guard.rank_collision_budget {K : Type*} [Field K] [DecidableEq K] {n s r c : ℕ}
    (A : Fin s → Matrix (Fin n) (Fin n) K)
    (hd : ∀ t i, A t i i ≠ 0) (hr : ∀ t, (A t).rank ≤ r)
    (hc : ∀ i j, i ≠ j → (Finset.univ.filter (fun t => A t i j ≠ 0)).card ≤ c) :
    2*s*n ≤ 2*s*r + n*(n-1)*c := by sorry
