import SigabaNeo.Trusted.Assumption

/-- Steering costs at most the number of patterns. Let `Ω` be the coins of a run (of a reduction
together with its challenger), weighted by `p`, let `P` be a finite set of answer patterns, and let
`win ω g` be the winning probability of the run on coins `ω` when the oracle answers follow the
pattern `g`. A prover that picks the pattern `m ω` after seeing the coins wins with probability at
most `|P|` times that of the efficient run that picks the pattern uniformly at random. In the note
`pq-we-reduction-query-flattening` this bounds what a cheating Merlin gains by choosing the answers
to the (few) uncertified oracle queries of a witness-encryption security reduction. -/
theorem AdvancedEncryption.WE.Reduction.steered_le_card_mul_guess {Ω P : Type} [Fintype Ω]
    [Fintype P] [Nonempty P] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (win : Ω → P → ℝ)
    (hwin : ∀ ω g, 0 ≤ win ω g) (m : Ω → P) :
    ∑ ω, p ω * win ω (m ω) ≤
      (Fintype.card P : ℝ) * ∑ ω, p ω * ((Fintype.card P : ℝ)⁻¹ * ∑ g, win ω g) := by sorry
