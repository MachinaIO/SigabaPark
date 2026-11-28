import Definitions.Def_GuardedBinaryProjection
import Mathlib.Tactic

theorem GuardedBinaryProjection.relativeFiber {W B : Type*} (block : W → B) (anchor : B → W) (sectionLaw : ∀ b, block (anchor b) = b)
    (r : W → Bool) (zeroAnchor : ∀ b, r (anchor b) = false) (accept : (W → Bool) → Prop) :
    (∃ w, GuardedBinaryProjection.encode block anchor w = r ∧ accept w) ↔
    ∃ y, accept (GuardedBinaryProjection.decode block r y) := by
  sorry
