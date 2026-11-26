import SigabaNeo.Trusted.Assumption

/-- Evaluation-only witness encryption: averaging over the planted witness. Some `w` has
`p w false + p w true ≤ 2q/|W|`; for it the decryptor with `w` hard-wired, run on encryptions of
the false statement, still has advantage `≥ 1 - ε - 2q/|W|`, so false-statement security at `k`
bits forces its cost to `2^k (1 - ε - 2q/|W|)^2`. See the note
`pq-we-concrete-regime-constructions`. -/
theorem AdvancedEncryption.WE.EvalOnly.query_lower_bound {W : Type*} [Fintype W] [Nonempty W]
    (E0 : Bool → PMF (List Bool)) (Ew : W → Bool → PMF (List Bool))
    (A : W → SigabaNeo.Machine) (p : W → Bool → ℝ) (q ε : ℝ) (k : ℕ)
    (hq : ∀ β, ∑ w, p w β ≤ q)
    (hcouple : ∀ w β, |(A w).acceptProb (E0 β) - (A w).acceptProb (Ew w β)| ≤ p w β)
    (hcorr : ∀ w, 1 - ε ≤ (A w).acceptProb (Ew w false) - (A w).acceptProb (Ew w true))
    (hsec : ∀ w, (2 : ℝ) ^ k * (SigabaNeo.Problem.decision (E0 false) (E0 true)).gain (A w) ≤
      ((A w).cost : ℝ))
    (hsmall : ε + 2 * q / (Fintype.card W : ℝ) ≤ 1) :
    ∃ w, (2 : ℝ) ^ k * (1 - ε - 2 * q / (Fintype.card W : ℝ)) ^ 2 ≤ ((A w).cost : ℝ) := by sorry
