import Definitions.Def_GuardedBinaryProjection
import Mathlib.Tactic

theorem solution {W B : Type*} (block : W → B) (anchor : B → W) (sectionLaw : ∀ b, block (anchor b) = b)
    (r : W → Bool) (zeroAnchor : ∀ b, r (anchor b) = false) (accept : (W → Bool) → Prop) :
    (∃ w, GuardedBinaryProjection.encode block anchor w = r ∧ accept w) ↔
    ∃ y, accept (GuardedBinaryProjection.decode block r y) := by
  constructor
  · rintro ⟨w,hw,ha⟩
    refine ⟨fun b => w (anchor b),?_⟩
    have he : GuardedBinaryProjection.decode block r (fun b => w (anchor b)) = w := by
      funext i
      rw [←hw]
      simp [GuardedBinaryProjection.decode, GuardedBinaryProjection.encode]
    rwa [he]
  · rintro ⟨y,hy⟩
    refine ⟨_,?_,hy⟩
    funext i
    simp [GuardedBinaryProjection.encode, GuardedBinaryProjection.decode, sectionLaw, zeroAnchor]
