import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **The overcomplete cut lemma (open; note `pq-we-masked-overcomplete-leaf` §10, PR #55).** Let
`1 ≤ L ≤ h` be such that the sub-CNF of the clauses inside the first `L` variables is already
unsatisfiable, while `2^{L−1}` exceeds the width `dR + w·n'` of the level matrices (one level past
the horizon of the cut lemma of §6). After CVW18 phase 1 and the leaf-first steps on the first-`L`
clause blocks (§6 steps 1–2), the truncated view `(W, D_1, …, D_L)` (`cutView … false`) is close to
the one in which every level-`L` target is an independent uniform matrix (`cutView … true`): under
decision LWE with `k` bits at the parameters `pL` of the regime, every machine has
`2^k · gain ≤ (2^L · hopLoss(L, t_rows))² · (cost + simCost)` (super-polynomially many hops, one
per prefix, are allowed). `t_rows = dR + w·n'`. -/
theorem AdvancedEncryption.WE.MaskedGGH15.overcomplete_cut (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (sh.dR + sh.w * sh.n') (min sh.dR sh.n') k pL)
    (hLWE : LWE.decision.HardAt pL k) (L : ℕ) (hL : 1 ≤ L) (hLh : L ≤ h)
    (hfirst : FirstUnsat Ψ L) (hover : sh.dR + sh.w * sh.n' < 2 ^ (L - 1)) :
    CloseAt (cutView p h sh Ψ r0 jC s0 L hLh false) (cutView p h sh Ψ r0 jC s0 L hLh true) k
      (2 ^ L * hopLoss L (sh.dR + sh.w * sh.n'))
      (simCost L (sh.dR + sh.w * sh.n') p.m p.q k) := by sorry
