import Definitions.Def_WE_LastPassGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15
open AdvancedEncryption.WE.LastPass

/-- **The regime-(d) walk from the equality-cube flip and the fat reroute (note
`pq-we-equality-cube-flip` §5).** For an unsatisfiable `Ψ` (every level string falsifies a
clause; for the multi-pass Tseitin CNF of a false statement this holds by `hEq` and `¬φ`), the
real view `(0, false)` and the final hybrid `(2^n, false)` (in which `mask` occurs only in the
challenge) are `CloseAt` with loss `2·2^n·(h+1)·hopLoss`: the `2·2^n` hops alternate
`equality_cube_flip` at `t` and `fat_reroute` from `t` to `t + 1`. -/
theorem AdvancedEncryption.WE.LastPass.lastpass_walk (p : Params) (h : ℕ) (sh : Shape)
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
    (hunsat : ∀ z : Fin h → Bool, ¬ Sat Ψ z) :
    CloseAt (lastPassView p h sh Ψ r0 jC s0 (h - n) 0 false)
      (lastPassView p h sh Ψ r0 jC s0 (h - n) (2 ^ n) false) k
      (2 * 2 ^ n * ((h + 1) * hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n)))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by sorry
