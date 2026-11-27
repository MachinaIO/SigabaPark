import Mathlib

theorem solution {V W : Type} [AddCommGroup V] [AddCommGroup W] [Finite V]
    (f : V →+ W) (d : W) :
    (∀ y : W, Nat.card {r : V // f r = y} = Nat.card {r : V // f r + d = y}) ↔
    ∃ s : V, f s = d := by
  classical
  constructor
  · intro h
    haveI : Nonempty {r : V // f r + d = d} := ⟨⟨0, by simp⟩⟩
    have pos : 0 < Nat.card {r : V // f r = d} := (h d).trans_gt Nat.card_pos
    obtain ⟨⟨s,hs⟩⟩ := (Nat.card_pos_iff.mp pos).1
    exact ⟨s,hs⟩
  · rintro ⟨s,hs⟩ y
    apply Nat.card_congr
    exact { toFun := fun r => ⟨r.val-s, by simp [map_sub,hs,r.property]⟩
            invFun := fun r => ⟨r.val+s, by simpa only [map_add,hs] using r.property⟩
            left_inv := fun r => Subtype.ext (by simp)
            right_inv := fun r => Subtype.ext (by simp) }
