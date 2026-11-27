import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic

theorem AdvancedEncryption.WE.FETree.exact_issuer_queries {A B : Type} [Fintype A] [Nontrivial B]
    (queries : (A → B) → Finset A) (emitter : (A → B) → A → B)
    (locality : ∀ f g, (∀ x ∈ queries f, f x = g x) → emitter f = emitter g)
    (exactness : ∀ f, emitter f = f) (f : A → B) :
    queries f = Finset.univ := by
  sorry
