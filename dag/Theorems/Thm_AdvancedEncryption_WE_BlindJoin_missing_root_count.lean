import Mathlib
open Polynomial Finset
open scoped BigOperators

theorem AdvancedEncryption.WE.BlindJoin.missing_root_count {K : Type*} [Field K] [DecidableEq K]
    (T : Finset K) (M B : ℕ) (hMB : M ≤ B) (D : Finset ℕ) (h : M ∉ D)
    (b : K) (hb : b ≠ 0) (a : ℕ → K)
    (hd : ∀ d ∈ D, d ≤ B) :
    (T.filter (fun x => b*x^M = ∑ d ∈ D, a d*x^d)).card ≤ B := by sorry
