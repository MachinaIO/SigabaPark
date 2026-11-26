import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **Flooding hides only short shifts (counting form).** For `t ≤ B`, the window `[0, B)` minus
its shift `[t, t + B)` has exactly `t` elements, so the statistical distance between the uniform
laws on the two windows is `t / B`. Hiding a shift `t` with advantage `2^{-λ}` needs a flooding
width `B ≥ 2^λ t`. A zero-entry crossing turns a short target into a uniform one (`t ≈ q/2`),
which would need `B > q` and destroy decryption (note `pq-we-zero-entry-crossing`, §5). -/
theorem AdvancedEncryption.WE.ZeroCross.shift_overlap_card (t B : ℕ) (h : t ≤ B) :
    (Finset.range B \ Finset.Ico t (t + B)).card = t := by sorry
