import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common

open Matrix

/-- **Decoded-defect attack on a two-sided hidden row (note `pq-we-two-sided-lwe`, §2.2).**
Over a field (in the attack, `Q`): prefix `x` has pad row `c x`, the two children of the cut have
invertible preimages `D₀, D₁`, the pad target noises are `E₀, E₁`, and `e x` is the prefix noise.
The decoded noise of child `b` is `c x ᵥ* E_b + e x ᵥ* D_b`, plus `f_b` on the chain prefix `t`
when the hidden row `δ` (`δ D_b = f_b`) is planted. If `c t` lies in the span of the other pad
rows (overcomplete cut), some combination `α` with `α t = 1` makes the summed defect
`N₀ D₀⁻¹ − N₁ D₁⁻¹` exactly `0` without `δ` and exactly `f₀ D₀⁻¹ − f₁ D₁⁻¹` with it. -/
theorem AdvancedEncryption.WE.TwoSided.decoded_defect_attack {K X κ μ : Type*} [Field K]
    [Fintype X] [DecidableEq X] [Fintype κ] [Fintype μ] [DecidableEq μ]
    (c : X → κ → K) (t : X)
    (hspan : c t ∈ Submodule.span K (Set.range fun x : {x : X // x ≠ t} => c x))
    (E₀ E₁ : Matrix κ μ K) (D₀ D₁ : Matrix μ μ K) (hD₀ : IsUnit D₀.det) (hD₁ : IsUnit D₁.det)
    (e : X → μ → K) (f₀ f₁ : μ → K) :
    ∃ α : X → K, α t = 1 ∧
      (∑ x, α x • ((c x ᵥ* E₀ + e x ᵥ* D₀) ᵥ* D₀⁻¹ - (c x ᵥ* E₁ + e x ᵥ* D₁) ᵥ* D₁⁻¹) = 0) ∧
      (∑ x, α x • ((c x ᵥ* E₀ + e x ᵥ* D₀ + (if x = t then f₀ else 0)) ᵥ* D₀⁻¹ -
          (c x ᵥ* E₁ + e x ᵥ* D₁ + (if x = t then f₁ else 0)) ᵥ* D₁⁻¹) =
        f₀ ᵥ* D₀⁻¹ - f₁ ᵥ* D₁⁻¹) := by sorry
