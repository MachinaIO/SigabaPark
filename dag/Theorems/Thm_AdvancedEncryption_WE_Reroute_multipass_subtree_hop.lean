import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **The per-threshold hop of the multi-pass positional walk (open; note
`pq-we-two-pass-reroute`, §7).** The level variables are `c ≥ 2` copies of `n` witness bits
(pass `p` reads witness bit `i` at level `p·n + i`) followed by any further levels (Tseitin gate
bits), `c·n ≤ h`. `Ψ` contains the `2n(c−1)` equality clauses `(z_{p·n+i} ∨ ¬z_{(p+1)·n+i})`,
`(¬z_{p·n+i} ∨ z_{(p+1)·n+i})`, so every string whose passes disagree falsifies a clause (no mixed
zeros), and anything else (for `Def_WE_CircuitSAT`: `Tseitin(φ)` on the last pass).

The comparator of `positionalView` reads all `h` levels; at the threshold `T = t·2^{h−n}` it
labels a string `mask'` iff the Gray rank of its pass-1 copy is `< t` (the eq chain continues as a
redundant chain below the pass-1 codeword of rank `t`). Moving from `T = t·2^{h−n}` to
`(t+1)·2^{h−n}` flips exactly the strings whose pass-1 copy is that codeword; the hypothesis
`hnw` says none of them satisfies `Ψ` (for the multi-pass Tseitin CNF this is `¬φ(t)`, a local,
checkable condition). The hop is one ERASE of that subtree followed by the two-pass reroute lemma
of PR #60 (§6 there): two collapses of redundant single-prefix chains (§1 of the note).

`hrank` (`rows^{2c−1} ≥ 2^{n/2}`) excludes the variable-partition rank attacks of CVW18 §9.3.2 /
Claim 9.8, whose honest-zero matrices have rank `≤ rows^{2c−1}`
(`AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le` for `c = 2`). Without it the statement
is expected to be false (two-repeating programs are distinguished asymptotically). Conclusion:
under decision LWE in the CVW18 regime, the hop loses at most `(h+1)·hopLoss`, i.e.
`poly(h)·ε_LWE`. Chaining `t = 0, …, 2^n − 1` with `hardAt_chain` connects the real view
(`T = 0`) to the final hybrid (`T = 2^h`). -/
theorem AdvancedEncryption.WE.Reroute.multipass_subtree_hop (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (3 * sh.dR + sh.w * sh.n' + sh.n) (min sh.dR (min sh.n' sh.n)) k pL)
    (hLWE : LWE.decision.HardAt pL k) (n c : ℕ) (hc : 2 ≤ c) (hcn : c * n ≤ h)
    (hEq : ∀ ps i : ℕ, ps + 1 < c → i < n →
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = ps * n + i ∧ b = true) ∨ ((a : ℕ) = (ps + 1) * n + i ∧ b = false))) ∧
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = ps * n + i ∧ b = false) ∨ ((a : ℕ) = (ps + 1) * n + i ∧ b = true))))
    (hrank : 2 ^ n ≤ (3 * sh.dR + sh.w * sh.n' + sh.n) ^ (2 * (2 * c - 1)))
    (t : ℕ) (ht : t < 2 ^ n)
    (hnw : ∀ z : Fin h → Bool,
      (∀ i : Fin h, (i : ℕ) < n → z i = grayCode h (t * 2 ^ (h - n)) i) → ¬ Sat Ψ z) :
    CloseAt (positionalView p h sh Ψ r0 jC s0 (t * 2 ^ (h - n)))
      (positionalView p h sh Ψ r0 jC s0 ((t + 1) * 2 ^ (h - n))) k
      ((h + 1) * hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
