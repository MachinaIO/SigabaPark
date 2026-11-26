import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

/-- **One decodable zero child suffices to detect a planted hidden row.** Work over `ℚ`. Let
`c x` be the secret rows of the prefixes `x` at a cut, and `α` an affine relation among them
(`∑ α x • c x = 0`, `α t = 1`) with common denominator `Δ`. Suppose a reduction can decode, below
one child, the exact integer noise of every prefix value along one common suffix with invertible
product `D`: `N x = c x M + e x D`, with `e x` the integer noise at the cut and `M` any matrix (the
deeper noise terms are linear in the prefix row). Then `Δ • ∑ α x • N x D⁻¹` is an integer vector.
If instead the chain prefix `t` carries a hidden uniform row `δ` with `δ D = f` small (the
redundant-chain hybrid of `pq-we-two-pass-reroute`), its decoded noise contains `f`, and the same
statistic equals that integer vector plus `Δ • f D⁻¹`, which is not integral for generic `f`.
So the decoded-defect barrier of PR #84 holds already with one decodable child: the two-child
cancellation is not needed. -/
theorem AdvancedEncryption.WE.FlipShift.one_child_integrality {X κ μ : Type*} [Fintype X] [DecidableEq X] [Fintype κ] [Fintype μ]
    [DecidableEq μ] (c : X → κ → ℚ) (t : X) (α : X → ℚ) (hαt : α t = 1)
    (hrel : ∑ x, α x • c x = 0)
    (Δ : ℤ) (hΔ : ∀ x, ∃ a : ℤ, (Δ : ℚ) * α x = a)
    (M : Matrix κ μ ℚ) (D : Matrix μ μ ℚ) (hD : IsUnit D.det)
    (e : X → μ → ℤ) (f : μ → ℚ) :
    ∃ z : μ → ℤ,
      (Δ : ℚ) • (∑ x, α x • ((c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D) ᵥ* D⁻¹)) =
        (fun j => (z j : ℚ)) ∧
      (Δ : ℚ) • (∑ x, α x • ((c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D +
          (if x = t then f else 0)) ᵥ* D⁻¹)) =
        (fun j => (z j : ℚ)) + (Δ : ℚ) • (f ᵥ* D⁻¹) := by sorry
