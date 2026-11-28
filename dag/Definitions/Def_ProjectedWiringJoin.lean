import Mathlib.Logic.Equiv.Defs

namespace ProjectedWiringJoin

/-- Both fixed-width bit arrays are public. Unused slots are zero.
Local eligibility is independent of the payload. -/
def issue {Z : Type*} (L R : Z → Bool) (b : Bool) (coins : Z → Bool) :
    (Z → Bool) × (Z → Bool) :=
  (fun z => L z && coins z, fun z => R z && (coins z ^^ b))

def couple {Z : Type*} (R : Z → Bool) (coins : Z → Bool) : Z → Bool :=
  fun z => coins z ^^ R z

theorem coupleTwice {Z : Type*} (R coins : Z → Bool) :
    couple R (couple R coins) = coins := by
  funext z
  cases hr : R z <;> cases hc : coins z <;> simp [couple, hr, hc]

/-- A bijection of the entire random tape, including unused labels. -/
def coinEquiv {Z : Type*} (R : Z → Bool) : (Z → Bool) ≃ (Z → Bool) where
  toFun := couple R
  invFun := couple R
  left_inv := coupleTwice R
  right_inv := coupleTwice R

theorem exactNo {Z : Type*} (L R coins : Z → Bool)
    (h : ∀ z, L z = true → R z = false) :
    issue L R true (coinEquiv R coins) = issue L R false coins := by
  apply Prod.ext
  · funext z
    cases hl : L z with
    | false => simp [issue, hl]
    | true => simp [issue, hl, coinEquiv, couple, h z hl]
  · funext z
    cases hr : R z <;> cases hc : coins z <;> simp [issue, coinEquiv, couple, hr, hc]

theorem sharedDecodes {Z : Type*} (L R coins : Z → Bool) (b : Bool) (z : Z)
    (hl : L z = true) (hr : R z = true) :
    ((issue L R b coins).1 z ^^ (issue L R b coins).2 z) = b := by
  cases hc : coins z <;> cases b <;> simp [issue, hl, hr, hc]

/-- A collision after a public compression gives disjoint conditional supports,
even when the two runs used independently chosen tapes. -/
theorem collisionSeparates {Z : Type*} (L R : Z → Bool) (z : Z)
    (hl : L z = true) (hr : R z = true) (c d : Z → Bool) :
    issue L R false c ≠ issue L R true d := by
  intro he
  have eq := congrArg (fun v : (Z → Bool) × (Z → Bool) => v.1 z ^^ v.2 z) he
  have a := sharedDecodes L R c false z hl hr
  have b := sharedDecodes L R d true z hl hr
  exact Bool.noConfusion (a.symm.trans (eq.trans b))

end ProjectedWiringJoin
