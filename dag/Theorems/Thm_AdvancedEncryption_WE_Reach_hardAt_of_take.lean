import SigabaNeo.Trusted.Assumption

open SigabaNeo

theorem AdvancedEncryption.WE.Reach.hardAt_of_take (D D' : PMF (List Bool)) (m k : ℕ)
    (h : D.map (List.take m) = D'.map (List.take m)) (hk : (2 : ℝ) ^ k ≤ m + 1) :
    (Problem.decision D D').HardAt k := by sorry
