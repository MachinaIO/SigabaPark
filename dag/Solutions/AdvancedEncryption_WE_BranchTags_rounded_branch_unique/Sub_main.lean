import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Int

theorem solution
    (q p tolerance d d' t t' : ℤ) (hq : 0 < q) (hsep : 2 * tolerance < q)
    (h₀ : |p * d - q * t| ≤ tolerance) (h₁ : |p * d' - q * t'| ≤ tolerance)
    (hsame : q ∣ d - d') (hrange : |t - t'| < p) : t = t' := by
  obtain ⟨k, hk⟩ := hsame
  let e := (p * d - q * t) - (p * d' - q * t')
  have he : e = q * (p * k - (t - t')) := by
    dsimp [e]
    linear_combination p * hk
  have hsmall : |e| < q := by
    have ha := abs_le.mp h₀
    have hb := abs_le.mp h₁
    dsimp [e]
    exact abs_lt.mpr (by constructor <;> omega)
  have hz := Int.eq_zero_of_abs_lt_dvd (show q ∣ e from ⟨_, he⟩) hsmall
  rw [he] at hz
  have hmult := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hq)
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd ⟨k, by omega⟩ hrange)
