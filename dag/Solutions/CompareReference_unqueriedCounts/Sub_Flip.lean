import Definitions.Def_CompareReference
import Mathlib.Tactic

open CompareReference

private theorem same {X : Type*} [DecidableEq X] (x : X) (f : X → Bool)
    (p : Probe X) (h : x ∉ (transcript f p).1) :
    transcript (CompareReference.flip x f) p = transcript f p := by
  induction p with
  | leaf b => rfl
  | ask i next ih =>
    simp only [transcript, List.mem_cons, not_or] at h
    have a : CompareReference.flip x f i = f i := by simp [CompareReference.flip, Ne.symm h.1]
    simp only [transcript, a, ih (f i) h.2]

private theorem exchange {X : Type*} [DecidableEq X] (x : X) (p : Probe X)
    (f : X → Bool) (b : Bool) (h : event x p b f) : event x p (!b) (CompareReference.flip x f) := by
  obtain ⟨hn, he⟩ := h
  unfold event
  rw [same x f p hn]
  refine ⟨hn, ?_⟩
  simp only [CompareReference.flip]
  rw [← he]
  cases (transcript f p).2 <;> cases (f x) <;> rfl

private theorem twice {X : Type*} [DecidableEq X] (x : X) (f : X → Bool) :
    CompareReference.flip x (CompareReference.flip x f) = f := by
  funext i
  by_cases h : i = x <;> simp [CompareReference.flip, h]

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (x : X) (p : CompareReference.Probe X) :
    Nat.card {f : X → Bool // CompareReference.event x p true f} =
    Nat.card {f : X → Bool // CompareReference.event x p false f} := by
  apply Nat.card_congr
  exact {
    toFun := fun f => ⟨CompareReference.flip x f.val, exchange x p f.val true f.property⟩
    invFun := fun f => ⟨CompareReference.flip x f.val, exchange x p f.val false f.property⟩
    left_inv := fun f => Subtype.ext (twice x f.val)
    right_inv := fun f => Subtype.ext (twice x f.val)
  }
