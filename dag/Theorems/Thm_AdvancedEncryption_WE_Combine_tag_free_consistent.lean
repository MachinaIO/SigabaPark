import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

/-- **Whole-string consistency tags (note `pq-we-hybrid-tool-combinations`, §3 and §8).** In a two-pass encoding, the evaluation that reads `a` in pass 1 and `b` in pass 2 is `m + h a − h b − C₁ a − C₂ b` (mask, whole-string tag, constraint parts). A linear combination with integer coefficients `c j` that cancels the formal coefficient of every tag value `h x` equals, exactly, the combination of *consistent* evaluations `m − C₁ x − C₂ x` with weights `ω x = Σ_{a j = x} c j`. So with generic tags, mixing passes gives a linear (zeroizing-type) attacker nothing beyond consistent strings. -/
theorem AdvancedEncryption.WE.Combine.tag_free_consistent {S J M : Type*} [DecidableEq S] [AddCommGroup M]
    (P : Finset J) (X : Finset S) (a b : J → S) (c : J → ℤ)
    (ha : ∀ j ∈ P, a j ∈ X) (hb : ∀ j ∈ P, b j ∈ X)
    (m : M) (h C₁ C₂ : S → M)
    (htag : ∀ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j)
        = ∑ j ∈ P.filter (fun j => b j = x), c j) :
    ∑ j ∈ P, c j • (m + h (a j) - h (b j) - C₁ (a j) - C₂ (b j))
      = ∑ x ∈ X, (∑ j ∈ P.filter (fun j => a j = x), c j) • (m - C₁ x - C₂ x) := by sorry
