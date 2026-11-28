import Definitions.Def_LatticeAttack_Research_Wall1_CandidateInputPairs
import Definitions.Def_LatticeAttack_Research_Wall1_OrderedFiberTuples

set_option autoImplicit true

/-! Exact ordered triple counting by input fibers. -/
namespace SigabaNeo.Wall1.CandidateInputPairs
open Finset
variable {α β : Type*} [DecidableEq β]

/-- Third power sum of input-fiber sizes, including repeated candidates. -/
def inputCubeSum (T : Finset α) (f : α → β) : ℕ :=
  ∑ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card)^3

/-- All-equal inputs give the third power sum. -/
theorem same_input_triples_card (T : Finset α) (f : α → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.1 = f p.1.2 ∧ f p.1.2 = f p.2).card =
      inputCubeSum T f := by
  let S := ((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.1 = f p.1.2 ∧ f p.1.2 = f p.2
  have hmap : (S : Set ((α × α) × α)).MapsTo (fun p ↦ f p.1.1) (T.image f) := by
    intro p hp
    exact mem_image_of_mem f (mem_product.mp (mem_product.mp (mem_filter.mp hp).1).1).1
  change S.card = _
  rw [card_eq_sum_card_fiberwise hmap]
  unfold inputCubeSum
  apply sum_congr rfl
  intro s hs
  have hfiber : (S.filter fun p ↦ f p.1.1 = s) =
      ((T.filter fun z ↦ f z = s) ×ˢ (T.filter fun z ↦ f z = s)) ×ˢ
        (T.filter fun z ↦ f z = s) := by
    ext p
    simp only [S, mem_filter, mem_product]
    constructor <;> intro h
    · rcases h with ⟨⟨⟨⟨ha, hb⟩, hc⟩, hab, hbc⟩, hfa⟩
      exact ⟨⟨⟨ha, hfa⟩, ⟨hb, hab.symm.trans hfa⟩⟩,
        ⟨hc, hbc.symm.trans (hab.symm.trans hfa)⟩⟩
    · rcases h with ⟨⟨⟨ha, hfa⟩, ⟨hb, hfb⟩⟩, ⟨hc, hfc⟩⟩
      exact ⟨⟨⟨⟨ha, hb⟩, hc⟩, hfa.trans hfb.symm, hfb.trans hfc.symm⟩, hfa⟩
  rw [hfiber, card_product, card_product]
  ring

private theorem first_two_equal_card (T : Finset α) (f : α → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.1 = f p.1.2).card =
      inputSquareSum T f * T.card := by
  have he : (((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.1 = f p.1.2) =
      ((T ×ˢ T).filter fun p ↦ f p.1 = f p.2) ×ˢ T := by
    ext p
    simp only [mem_filter, mem_product]
    tauto
  rw [he, card_product, same_input_pairs_card]

private theorem first_third_equal_card (T : Finset α) (f : α → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.1 = f p.2).card =
      inputSquareSum T f * T.card := by
  rw [← first_two_equal_card]
  apply card_bij (fun p _ ↦ ((p.1.1, p.2), p.1.2))
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    tauto
  · intro a ha b hb h
    rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
    rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
    simp only [Prod.mk.injEq] at h ⊢
    tauto
  · intro b hb
    refine ⟨((b.1.1, b.2), b.1.2), ?_, rfl⟩
    simp only [mem_filter, mem_product] at hb ⊢
    tauto

private theorem last_two_equal_card (T : Finset α) (f : α → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ f p.1.2 = f p.2).card =
      inputSquareSum T f * T.card := by
  rw [← first_two_equal_card]
  apply card_bij (fun p _ ↦ ((p.1.2, p.2), p.1.1))
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    tauto
  · intro a ha b hb h
    exact Prod.ext (Prod.ext (congrArg Prod.snd h) (congrArg (fun p ↦ p.1.1) h))
      (congrArg (fun p ↦ p.1.2) h)
  · intro b hb
    refine ⟨((b.2, b.1.1), b.1.2), ?_, rfl⟩
    simp only [mem_filter, mem_product] at hb ⊢
    tauto

/-- Inclusion-exclusion without truncated natural subtraction. -/
theorem different_input_triples_card_add (T : Finset α) (f : α → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦
      f p.1.1 ≠ f p.1.2 ∧ f p.1.1 ≠ f p.2 ∧ f p.1.2 ≠ f p.2).card +
      3 * T.card * inputSquareSum T f = T.card^3 + 2 * inputCubeSum T f := by
  have hp (p : (α × α) × α) :
      (if f p.1.1 ≠ f p.1.2 ∧ f p.1.1 ≠ f p.2 ∧ f p.1.2 ≠ f p.2 then 1 else 0) +
      (if f p.1.1 = f p.1.2 then 1 else 0) +
      (if f p.1.1 = f p.2 then 1 else 0) +
      (if f p.1.2 = f p.2 then 1 else 0) =
      1 + 2 * (if f p.1.1 = f p.1.2 ∧ f p.1.2 = f p.2 then 1 else 0 : ℕ) := by
    by_cases hab : f p.1.1 = f p.1.2 <;>
      by_cases hac : f p.1.1 = f p.2 <;>
      by_cases hbc : f p.1.2 = f p.2 <;> simp_all
  have h := sum_congr rfl (fun p (_ : p ∈ ((T ×ˢ T) ×ˢ T)) ↦ hp p)
  simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one,
    ← mul_sum, card_product] at h
  rw [first_two_equal_card, first_third_equal_card, last_two_equal_card,
    same_input_triples_card] at h
  nlinarith

/-- Real-valued form for insertion into factorial moment identities. -/
theorem different_input_triples_card_real (T : Finset α) (f : α → β) :
    ((((T ×ˢ T) ×ˢ T).filter fun p ↦
      f p.1.1 ≠ f p.1.2 ∧ f p.1.1 ≠ f p.2 ∧ f p.1.2 ≠ f p.2).card : ℝ) =
      (T.card : ℝ)^3 - 3 * T.card * inputSquareSum T f + 2 * inputCubeSum T f := by
  have h := different_input_triples_card_add T f
  have hr : ((((T ×ˢ T) ×ˢ T).filter fun p ↦
      f p.1.1 ≠ f p.1.2 ∧ f p.1.1 ≠ f p.2 ∧ f p.1.2 ≠ f p.2).card : ℝ) +
      3 * T.card * inputSquareSum T f = (T.card : ℝ)^3 + 2 * inputCubeSum T f := by
    exact_mod_cast h
  linarith

open scoped Classical
open OrderedFiberTuples

/-- Three distinct-input embeddings are exactly the ordered product triples. -/
theorem ordered_distinct_input_triples_card (T : Finset α) (f : α → β) :
    ((univ : Finset (orderedTuples T 3)).filter
      (fun e ↦ Function.Injective (fun i ↦ f (e i).val))).card =
    (((T ×ˢ T) ×ˢ T).filter fun p ↦
      f p.1.1 ≠ f p.1.2 ∧ f p.1.1 ≠ f p.2 ∧ f p.1.2 ≠ f p.2).card := by
  apply card_bij (fun e _ ↦ (((e 0).val, (e 1).val), (e 2).val))
  · intro e he
    have hi := (mem_filter.mp he).2
    simp only [mem_filter, mem_product]
    refine ⟨⟨⟨(e 0).property, (e 1).property⟩, (e 2).property⟩, ?_, ?_, ?_⟩
    · exact fun h ↦ (by decide : (0 : Fin 3) ≠ 1) (hi h)
    · exact fun h ↦ (by decide : (0 : Fin 3) ≠ 2) (hi h)
    · exact fun h ↦ (by decide : (1 : Fin 3) ≠ 2) (hi h)
  · intro a ha b hb h
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    fin_cases i
    · exact congrArg (fun p ↦ p.1.1) h
    · exact congrArg (fun p ↦ p.1.2) h
    · exact congrArg Prod.snd h
  · intro p hp
    rcases mem_filter.mp hp with ⟨hmem, hab, hac, hbc⟩
    rcases mem_product.mp hmem with ⟨habmem, hcmem⟩
    rcases mem_product.mp habmem with ⟨hamem, hbmem⟩
    let v : Fin 3 → T := ![⟨p.1.1, hamem⟩, ⟨p.1.2, hbmem⟩, ⟨p.2, hcmem⟩]
    have hv : Function.Injective (fun i ↦ f (v i).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [v, eq_comm]
    let e : orderedTuples T 3 := ⟨v, fun _ _ h ↦ hv (congrArg (fun z : T ↦ f z.val) h)⟩
    refine ⟨e, mem_filter.mpr ⟨mem_univ _, hv⟩, ?_⟩
    rfl

/-- The distinct-input ordered tuple count in the factorial-moment index format. -/
theorem ordered_distinct_input_triples_card_real (T : Finset α) (f : α → β) :
    (((univ : Finset (orderedTuples T 3)).filter
      (fun e ↦ Function.Injective (fun i ↦ f (e i).val))).card : ℝ) =
      (T.card : ℝ)^3 - 3 * T.card * inputSquareSum T f + 2 * inputCubeSum T f := by
  rw [ordered_distinct_input_triples_card]
  exact different_input_triples_card_real T f

end SigabaNeo.Wall1.CandidateInputPairs
#print axioms SigabaNeo.Wall1.CandidateInputPairs.same_input_triples_card
#print axioms SigabaNeo.Wall1.CandidateInputPairs.different_input_triples_card_add
#print axioms SigabaNeo.Wall1.CandidateInputPairs.different_input_triples_card_real
#print axioms SigabaNeo.Wall1.CandidateInputPairs.ordered_distinct_input_triples_card_real
