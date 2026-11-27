import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic

theorem solution {A B : Type} [Fintype A] [Nontrivial B]
    (queries : (A → B) → Finset A) (emitter : (A → B) → A → B)
    (locality : ∀ f g, (∀ x ∈ queries f, f x = g x) → emitter f = emitter g)
    (exactness : ∀ f, emitter f = f) (f : A → B) :
    queries f = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro x
  by_contra hx
  obtain ⟨b, hb⟩ := exists_ne (f x)
  let g := fun a => if a = x then b else f a
  have agree : ∀ y ∈ queries f, f y = g y := by
    intro y hy
    have hxy : y ≠ x := fun e => hx (e ▸ hy)
    simp [g, hxy]
  have he : f = g := (exactness f).symm.trans ((locality f g agree).trans (exactness g))
  have hx' := congrFun he x
  exact hb (by simpa [g] using hx'.symm)
