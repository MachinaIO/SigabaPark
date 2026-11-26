import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **The PLR hop of the positional masked γ⊗-GGH15 candidate (open; note
`pq-we-masked-evaluator-mechanisms` §3, PR #54).** Let path `t` (the reflected Gray codeword of
rank `t < 2^h`) be a non-witness of `Ψ`. Then hybrids `t` and `t + 1` of `positionalView` (the
comparator threshold moves past path `t`, whose final comparator row changes from `mask` to
`mask'`) are close: under decision LWE with `k` bits at the parameters `pL` of the regime
(CVW18-type conditions, `Regime`), every machine has
`2^k · gain ≤ hopLoss(h, t_rows)² · (cost + simCost)`, i.e. the hop loses `poly(h)·ε_LWE`.
`t_rows = 3·dR + w·n' + n` is the number of rows of the level matrices. The public left
vectors read every clause (`j_C` has no zero entry) and `r₀`, `s'₀` are non-zero. -/
theorem AdvancedEncryption.WE.MaskedGGH15.plr_hop (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (3 * sh.dR + sh.w * sh.n' + sh.n) (min sh.dR (min sh.n' sh.n)) k pL)
    (hLWE : LWE.decision.HardAt pL k) (t : ℕ) (ht : t < 2 ^ h)
    (hnw : ¬ Sat Ψ (grayCode h t)) :
    CloseAt (positionalView p h sh Ψ r0 jC s0 t) (positionalView p h sh Ψ r0 jC s0 (t + 1)) k
      (hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
