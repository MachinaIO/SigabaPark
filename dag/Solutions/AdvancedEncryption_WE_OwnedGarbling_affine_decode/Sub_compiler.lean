import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution {I : Type} [Fintype I] (theta pi a r : I → ZMod 2) (c s : ZMod 2) :
    c + (∑ i, pi i * (a i + r i)) + s =
    (c + ∑ i, theta i * a i) + (∑ i, (theta i + pi i) * (a i + r i)) +
      (s + ∑ i, theta i * r i) := by
  have h : ∀ i, (theta i + pi i)*(a i+r i) =
    theta i*a i + theta i*r i + pi i*(a i+r i) := by intro i; ring
  simp_rw [h]
  simp only [Finset.sum_add_distrib]
  have z (x : ZMod 2) : x+x=0 := CharTwo.add_self_eq_zero x
  linear_combination -(z (∑ i, theta i*a i)) - (z (∑ i, theta i*r i))
