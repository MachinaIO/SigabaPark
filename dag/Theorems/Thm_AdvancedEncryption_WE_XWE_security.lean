import Definitions.Def_WE_XWE

open SigabaNeo AdvancedEncryption.WE.XWE

theorem AdvancedEncryption.WE.XWE.security (S : ABELaws) (W1 W2 : List (List Bool))
    (post : List Bool → List Bool) (k : ℕ)
    (hop : ∀ j < W2.length,
      (Problem.decision (hybLaw S W1 W2 post j) (hybLaw S W1 W2 post (j + 1))).HardAt k)
    (A : Machine) :
    (2 : ℝ) ^ k *
        (Problem.decision (xweLaw S W1 W2 post false) (xweLaw S W1 W2 post true)).gain A ≤
      (W2.length : ℝ) ^ 2 * A.cost := by sorry
