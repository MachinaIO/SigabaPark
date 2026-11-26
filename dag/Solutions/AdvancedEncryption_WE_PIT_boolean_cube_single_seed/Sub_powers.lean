import SigabaNeoStd

open Finset Polynomial

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (c : Finset ℕ → K) :
    let V := range m
    let idx := fun T : Finset ℕ ↦ ∑ i ∈ T, 2 ^ i
    let p : K[X] := ∑ T ∈ V.powerset, monomial (idx T) (c T)
    let sat := ∃ S ⊆ V, (∑ T ∈ S.powerset, c T) ≠ 0
    (¬sat → ∀ a : K, p.eval a = 0) ∧
      (sat → (univ.filter fun a : K ↦ p.eval a = 0).card ≤ 2 ^ m - 1) := by
  classical
  dsimp only
  let V := range m
  let idx := fun T : Finset ℕ ↦ ∑ i ∈ T, 2 ^ i
  let p : K[X] := ∑ T ∈ V.powerset, monomial (idx T) (c T)
  have hi : Function.Injective idx := geomSum_injective (n := 2) (by decide)
  have hc (T : Finset ℕ) (hT : T ⊆ V) : p.coeff (idx T) = c T := by
    simp only [p, ← lcoeff_apply, map_sum]
    simp only [lcoeff_apply, coeff_monomial]
    rw [sum_eq_single T]
    · simp
    · intro U _hne hu
      simp [hi.ne hu]
    · simp [mem_powerset.mpr hT]
  constructor
  · intro h
    push Not at h
    have zero (T : Finset ℕ) : T ⊆ V → c T = 0 := by
      induction T using Finset.strongInductionOn
      rename_i T ih
      intro hT
      have hh := h T hT
      rw [sum_eq_single T] at hh
      · exact hh
      · intro U hU hne
        have hu := mem_powerset.mp hU
        exact ih U (Finset.ssubset_iff_subset_ne.mpr ⟨hu,hne⟩) (hu.trans hT)
      · simp
    have hp : p = 0 := sum_eq_zero fun T hT ↦ by simp [zero T (mem_powerset.mp hT)]
    intro a
    change p.eval a = 0
    rw [hp, eval_zero]
  · rintro ⟨S, hS, hs⟩
    have hp : p ≠ 0 := by
      intro hp
      apply hs
      apply sum_eq_zero
      intro T hT
      simpa [hp] using (hc T ((mem_powerset.mp hT).trans hS)).symm
    have hd : p.natDegree ≤ 2^m-1 := by
      apply natDegree_sum_le_of_forall_le
      intro T hT
      refine (natDegree_monomial_le _).trans ?_
      calc
        idx T ≤ ∑ i ∈ V, 2^i := sum_le_sum_of_subset_of_nonneg (mem_powerset.mp hT) (by simp)
        _ = _ := by simp [V, Nat.geomSum_eq (m := 2) (by decide)]
    have roots : (univ.filter fun a : K ↦ p.eval a = 0) ⊆ p.roots.toFinset := by
      intro a ha
      exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (mem_filter.mp ha).2)
    exact (card_le_card roots).trans (p.roots.toFinset_card_le.trans ((card_roots' p).trans hd))
