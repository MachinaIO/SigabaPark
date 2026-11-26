import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **The masked two-vector lemma (open; note `pq-we-witness-prf-masked-evaluator` §6, PR #45).**
For an unsatisfiable CNF `Ψ`, the masked γ⊗-GGH15 view with the mask,
`(u_O, u_C, {D_{i,b}}, mask)`, is close to the same view with a uniform vector in place of the
mask: under decision LWE with `k` bits at the parameters `pL` of the regime, every machine has
`2^k · gain ≤ (2^h · hopLoss(h, t_rows))² · (cost + simCost)`, the loss
`2^{|w|} · poly(h) · ε_LWE` of witness-indexed hops allowed by PR #45 (`h` levels read the
witness and the Tseitin gate bits). `t_rows = dR + w·n' + n`. -/
theorem AdvancedEncryption.WE.MaskedGGH15.masked_two_vector (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (sh.dR + sh.w * sh.n' + sh.n) (min sh.dR (min sh.n' sh.n)) k pL)
    (hLWE : LWE.decision.HardAt pL k) (hunsat : ∀ x, ¬ Sat Ψ x) :
    CloseAt (maskedReal p h sh Ψ r0 jC s0) (maskedIdeal p h sh Ψ r0 jC s0) k
      (2 ^ h * hopLoss h (sh.dR + sh.w * sh.n' + sh.n))
      (simCost h (sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
