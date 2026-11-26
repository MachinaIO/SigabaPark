import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

theorem solution {S J M : Type*} [DecidableEq S] [AddCommGroup M]
    (P : Finset J) (X : Finset S) (a b : J → S) (c : J → ℤ)
    (ha : ∀ j ∈ P, a j ∈ X) (hb : ∀ j ∈ P, b j ∈ X)
    (m : M) (h C₁ C₂ : S → M)
    (htag : ∀ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j)
        = ∑ j ∈ P.filter (fun j => b j = x), c j) :
    ∑ j ∈ P, c j • (m + h (a j) - h (b j) - C₁ (a j) - C₂ (b j))
      = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • (m - C₁ x - C₂ x) := by
  have key : ∀ (e : J → S), (∀ j ∈ P, e j ∈ X) → ∀ f : S → M,
      ∑ j ∈ P, c j • f (e j) = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => e j = x), c j) • f x := by
    intro e he f
    rw [← Finset.sum_fiberwise_of_maps_to (g := e) he]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [(Finset.mem_filter.mp hj).2]
  have hm : ∑ j ∈ P, c j • m = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • m :=
    key a ha (fun _ => m)
  have h1 := key a ha h
  have h2 := key b hb h
  have h3 := key a ha C₁
  have h4 := key b hb C₂
  have h2' : ∑ j ∈ P, c j • h (b j) = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • h x := by
    rw [h2]; exact Finset.sum_congr rfl (fun x hx => by rw [htag x hx])
  have h4' : ∑ j ∈ P, c j • C₂ (b j) = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • C₂ x := by
    rw [h4]; exact Finset.sum_congr rfl (fun x hx => by rw [htag x hx])
  have lhs : ∑ j ∈ P, c j • (m + h (a j) - h (b j) - C₁ (a j) - C₂ (b j))
      = ∑ j ∈ P, c j • m + ∑ j ∈ P, c j • h (a j) - ∑ j ∈ P, c j • h (b j)
        - ∑ j ∈ P, c j • C₁ (a j) - ∑ j ∈ P, c j • C₂ (b j) := by
    simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have rhs : ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • (m - C₁ x - C₂ x)
      = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • m
        - ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • C₁ x
        - ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • C₂ x := by
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [lhs, rhs, hm, h1, h2', h3, h4']
  abel
