import Definitions.Def_WE_LastPassGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15
open AdvancedEncryption.WE.LastPass

/-- **The fat reroute (open; note `pq-we-equality-cube-flip` §5).** Same scheme as
`AdvancedEncryption.WE.LastPass.equality_cube_flip`. Hybrid `(t, true)` (eq leaf already
labelled `mask'`) and hybrid `(t + 1, false)` give the same label to every level string (Gray
rank of the last copy `≤ t` ↦ `mask'`); they differ only in the comparator's class structure on
the last copy, whose chain classes are reached by all `2^{h−n}` prefixes. The claim: the
functionality-preserving re-encoding `(t, true) → (t + 1, false)` is `CloseAt` under decision
LWE with loss `(h+1)·hopLoss`, for every `Ψ` (no hypothesis on `φ`: the labels agree).

`hrank` (`rows^{2(2c−1)} ≥ 2^n`) excludes the variable-partition rank tests of CVW18 §9.3.2 /
Claim 9.8, as in `AdvancedEncryption.WE.Reroute.multipass_subtree_hop` (open PR #61); without it
the statement is expected to be false. The witness-pair consistency barrier of PR #61 §4 applies
to it (witnesses lie below the chain classes of the last copy). -/
theorem AdvancedEncryption.WE.LastPass.fat_reroute (p : Params) (h : ℕ) (sh : Shape)
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
    (hrank : 2 ^ n ≤ (3 * sh.dR + sh.w * sh.n' + sh.n) ^ (2 * (2 * c - 1)))
    (t : ℕ) (ht : t < 2 ^ n) :
    CloseAt (lastPassView p h sh Ψ r0 jC s0 (h - n) t true)
      (lastPassView p h sh Ψ r0 jC s0 (h - n) (t + 1) false) k
      ((h + 1) * hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
