import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **Departures from a cube partition its complement.** A string `z` lies outside the prefix
cube `p∗` (prefix length `l`) iff there is a level `j < l` at which `z` first differs from `p`. So
the departure cubes `p_{<j}(1 − p_j)∗` of the zero entries of a cube program cover exactly the
complement of `p∗`, and all of them are padded only when everything outside `p∗` is padded. In the
APG walk, some zero entry of every slot has live departures until the last hybrid
(note `pq-we-zero-entry-crossing`, §2). -/
theorem AdvancedEncryption.WE.ZeroCross.departure_first_difference {n : ℕ} (p z : Fin n → Bool) (l : ℕ) :
    (¬ ∀ i : Fin n, i.val < l → z i = p i) ↔
      ∃ j : Fin n, j.val < l ∧ (∀ i : Fin n, i.val < j.val → z i = p i) ∧ z j ≠ p j := by sorry
