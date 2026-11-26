import Definitions.Def_WE_LastPassGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15
open AdvancedEncryption.WE.LastPass

/-- **The equality-cube flip (open; note `pq-we-equality-cube-flip`, PR #60 §3(d)).** The level
variables are `c ≥ 2` copies of `n` witness bits laid out by `copyOff` (the last copy on the
last `n` levels, Tseitin gate bits in between), and `Ψ` contains the `2n(c−1)` equality clauses
between consecutive copies (`hEq`), so every string whose copies disagree falsifies a clause. The
comparator reads only the last copy (`lastPassView` with `o = h − n`): all `2^{h−n}` prefixes
reach its eq chain (a fat class).

Fix `t < 2^n` and assume `hnw`: no string whose last copy is the Gray codeword of rank `t`
(bit `i` of the last copy, at level `h − n + i`, is bit `n − 1 − i` of `t ⊕ ⌊t/2⌋`) satisfies
`Ψ`. By `hEq` this reduces to the consistent strings (`AdvancedEncryption.WE.LastPass.not_sat_of_copies_differ`);
for the multi-pass Tseitin CNF it is `¬φ(t)`, a local, checkable condition. The claim: flipping
the label of the eq leaf (from `mask` to `mask'`) is `CloseAt` under decision LWE with loss
`(h+1)·hopLoss`. The flip changes the value of the consistent string `(t, …, t)` and of its
`2^{(c−1)n} − 1` orphans at once (one equality cube per first mismatch position); none of them is
a zero, so no witness lies in the flipped class, and the class structure does not change. -/
theorem AdvancedEncryption.WE.LastPass.equality_cube_flip (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (3 * sh.dR + sh.w * sh.n' + sh.n) (min sh.dR (min sh.n' sh.n)) k pL)
    (hLWE : LWE.decision.HardAt pL k) (n c : ℕ) (hc : 2 ≤ c) (hcn : c * n ≤ h)
    (hEq : ∀ ps i : ℕ, ps + 1 < c → i < n →
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = copyOff h n c ps + i ∧ b = true) ∨
          ((a : ℕ) = copyOff h n c (ps + 1) + i ∧ b = false))) ∧
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = copyOff h n c ps + i ∧ b = false) ∨
          ((a : ℕ) = copyOff h n c (ps + 1) + i ∧ b = true))))
    (t : ℕ) (ht : t < 2 ^ n)
    (hnw : ∀ z : Fin h → Bool,
      (∀ i : Fin h, h - n ≤ (i : ℕ) → z i = Nat.testBit (t ^^^ t / 2) (h - 1 - (i : ℕ))) →
        ¬ Sat Ψ z) :
    CloseAt (lastPassView p h sh Ψ r0 jC s0 (h - n) t false)
      (lastPassView p h sh Ψ r0 jC s0 (h - n) t true) k
      ((h + 1) * hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
