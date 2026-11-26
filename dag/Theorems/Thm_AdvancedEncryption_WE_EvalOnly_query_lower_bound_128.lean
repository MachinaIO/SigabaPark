import SigabaNeo.Trusted.Assumption

/-- The evaluation-only lower bound at `|W| = 2^128`, `κ = 128` (so `ε ≤ 2^{-127}`), `λ = 128`:
an encryptor of query mass at most `2^125` leaves an adversary built from the decryptor with cost
at least `2^127`. See the note `pq-we-concrete-regime-constructions`. -/
theorem AdvancedEncryption.WE.EvalOnly.query_lower_bound_128 {W : Type*} [Fintype W] (hW : Fintype.card W = 2 ^ 128)
    (E0 : Bool → PMF (List Bool)) (Ew : W → Bool → PMF (List Bool))
    (A : W → SigabaNeo.Machine) (p : W → Bool → ℝ) (q ε : ℝ)
    (hq : ∀ β, ∑ w, p w β ≤ q) (hq125 : q ≤ 2 ^ 125) (hε : ε ≤ (2 ^ 127 : ℝ)⁻¹)
    (hcouple : ∀ w β, |(A w).acceptProb (E0 β) - (A w).acceptProb (Ew w β)| ≤ p w β)
    (hcorr : ∀ w, 1 - ε ≤ (A w).acceptProb (Ew w false) - (A w).acceptProb (Ew w true))
    (hsec : ∀ w, (2 : ℝ) ^ 128 * (SigabaNeo.Problem.decision (E0 false) (E0 true)).gain (A w) ≤
      ((A w).cost : ℝ)) :
    ∃ w, (2 : ℝ) ^ 127 ≤ ((A w).cost : ℝ) := by sorry
