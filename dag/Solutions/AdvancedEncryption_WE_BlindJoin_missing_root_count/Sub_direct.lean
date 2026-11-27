import Mathlib
open Polynomial Finset
open scoped BigOperators

theorem solution {K : Type*} [Field K] [DecidableEq K]
    (T : Finset K) (M B : ℕ) (hMB : M ≤ B) (D : Finset ℕ) (h : M ∉ D)
    (b : K) (hb : b ≠ 0) (a : ℕ → K)
    (hd : ∀ d ∈ D, d ≤ B) :
    (T.filter (fun x => b*x^M = ∑ d ∈ D, a d*x^d)).card ≤ B := by
  let P : K[X] := monomial M b - ∑ d ∈ D, monomial d (a d)
  have hz : P ≠ 0 := by
    intro z
    have := congrArg (fun f : K[X] => f.coeff M) z
    have hsum : (∑ d ∈ D, monomial d (a d)).coeff M = 0 := by
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro d hd
      exact coeff_monomial_of_ne _ (fun e => h (e ▸ hd))
    simp [P,hsum] at this
    exact hb this
  apply (card_le_degree_of_subset_roots (p := P) ?_).trans
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_monomial_le ..).trans hMB
    · apply natDegree_sum_le_of_forall_le
      intro d hu
      exact (natDegree_monomial_le ..).trans (hd d hu)
  · intro x hx
    rw [mem_roots hz,IsRoot]
    have hh := (Finset.mem_filter.mp hx).2
    simp [P, eval_finsetSum, eval_monomial, hh]
