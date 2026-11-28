import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic

set_option autoImplicit true

/-! Ordered distinct tuples in a finite fiber, including the empty tuple. -/
noncomputable section
namespace SigabaNeo.Wall1.OrderedFiberTuples
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- An ordered tuple of distinct candidates. -/
abbrev orderedTuples (T : Finset α) (h : ℕ) := Fin h ↪ T

/-- All entries of the tuple belong to the specified fiber. -/
def allHits (T : Finset α) (f : α → β) (c : β) (h : ℕ) :
    Finset (orderedTuples T h) :=
  univ.filter fun e ↦ ∀ i, f (e i).val = c

/-- Restriction to the fiber is an equivalence of ordered tuple types. -/
def fiberTupleEquiv (T : Finset α) (f : α → β) (c : β) (h : ℕ) :
    {e : orderedTuples T h // ∀ i, f (e i).val = c} ≃
      (Fin h ↪ (T.filter fun z ↦ f z = c)) where
  toFun e :=
    { toFun := fun i ↦ ⟨(e.val i).val, mem_filter.mpr ⟨(e.val i).property, e.property i⟩⟩
      inj' := by
        intro i j hij
        apply e.val.injective
        exact Subtype.ext (congrArg (fun z : ↥(T.filter fun z ↦ f z = c) ↦ (z : α)) hij) }
  invFun e :=
    ⟨{ toFun := fun i ↦ ⟨(e i).val, (mem_filter.mp (e i).property).1⟩
       inj' := by
         intro i j hij
         apply e.injective
         exact Subtype.ext (congrArg (fun z : ↥T ↦ (z : α)) hij) },
     fun i ↦ (mem_filter.mp (e i).property).2⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    rfl

/-- Fixed-label tuple count is exactly the falling factorial of its fiber size. -/
theorem allHits_card (T : Finset α) (f : α → β) (c : β) (h : ℕ) :
    (allHits T f c h).card = ((T.filter fun z ↦ f z = c).card).descFactorial h := by
  unfold allHits
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberTupleEquiv T f c h),
    Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]

/-- The empty tuple contributes one for every label, including labels with empty fibers. -/
theorem allHits_card_zero (T : Finset α) (f : α → β) (c : β) :
    (allHits T f c 0).card = 1 := by
  rw [allHits_card, Nat.descFactorial_zero]

/-- Summing over labels at degree zero counts labels, not one globally unique empty tuple. -/
theorem sum_allHits_card_zero [Fintype β] (T : Finset α) (f : α → β) :
    (∑ c : β, (allHits T f c 0).card) = Fintype.card β := by
  simp [allHits_card_zero]

end SigabaNeo.Wall1.OrderedFiberTuples
#print axioms SigabaNeo.Wall1.OrderedFiberTuples.allHits_card
#print axioms SigabaNeo.Wall1.OrderedFiberTuples.allHits_card_zero
#print axioms SigabaNeo.Wall1.OrderedFiberTuples.sum_allHits_card_zero
