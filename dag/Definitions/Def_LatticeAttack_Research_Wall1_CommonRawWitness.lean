import Definitions.Def_LatticeAttack_Research_Wall1_CosetOccupancy
import Mathlib.GroupTheory.Coset.Basic

set_option autoImplicit true

/-! # A common raw witness for every gated history entry

The label type is the fixed raw label space. Projected occupancies must first be pulled
back along their uniform quotient maps. A raw hit surviving at each eligible entry then
gives a single exceptional input set, rather than a sum of per-entry exceptions.

The lattice embedding, quotient maps, radius gate, and numerical raw moment bound are
separate obligations. This file proves the finite counting transfer, without a factor
equal to the number of entries and without independence assumptions.
-/

noncomputable section
namespace SigabaNeo.Wall1.CommonRawWitness
open Finset CosetOccupancy
open scoped Classical

/-- Preserving each occupied raw label can only decrease the empty-label count. -/
theorem emptyCount_le_of_preserves_hits {α : Type*} [Fintype α]
    (raw projected : α → ℕ)
    (preserves : ∀ c, raw c ≠ 0 → projected c ≠ 0) :
    emptyCount projected ≤ emptyCount raw := by
  apply card_le_card
  intro c hc
  apply mem_filter.mpr
  refine ⟨mem_univ c, ?_⟩
  by_contra hn
  exact preserves c hn ((mem_filter.mp hc).2)

/-- Every gated exit belongs to the same raw exceptional set, even with infinitely many
entry indices. Only the input and raw label spaces need to be finite. -/
theorem history_exit_count_le_raw {Ω ι α : Type*} [Fintype Ω] [Fintype α]
    (raw : Ω → α → ℕ) (projected : ι → Ω → α → ℕ) (gate : ι → Ω → Prop)
    (preserves : ∀ i ω, gate i ω → ∀ c, raw ω c ≠ 0 → projected i ω c ≠ 0)
    (a b : ℕ) :
    (univ.filter fun ω ↦ ∃ i, gate i ω ∧
      a * Fintype.card α ≤ b * emptyCount (projected i ω)).card ≤
    (univ.filter fun ω ↦ a * Fintype.card α ≤ b * emptyCount (raw ω)).card := by
  apply card_le_card
  intro ω hω
  obtain ⟨i, hg, hi⟩ := (mem_filter.mp hω).2
  apply mem_filter.mpr
  refine ⟨mem_univ ω, hi.trans ?_⟩
  exact Nat.mul_le_mul_left b
    (emptyCount_le_of_preserves_hits (raw ω) (projected i ω) (preserves i ω hg))

/-- A first raw moment bounds all gated exits together. There is no sum over entries. -/
theorem history_exit_first_moment {Ω ι α : Type*} [Fintype Ω] [Fintype α]
    (raw : Ω → α → ℕ) (projected : ι → Ω → α → ℕ) (gate : ι → Ω → Prop)
    (preserves : ∀ i ω, gate i ω → ∀ c, raw ω c ≠ 0 → projected i ω c ≠ 0)
    (a b : ℕ) :
    a * Fintype.card α *
      (univ.filter fun ω ↦ ∃ i, gate i ω ∧
        a * Fintype.card α ≤ b * emptyCount (projected i ω)).card ≤
    b * ∑ ω, emptyCount (raw ω) := by
  let bad : Finset Ω := univ.filter fun ω ↦
    a * Fintype.card α ≤ b * emptyCount (raw ω)
  have hcount := history_exit_count_le_raw raw projected gate preserves a b
  have hsum : a * Fintype.card α * bad.card ≤ ∑ ω ∈ bad, b * emptyCount (raw ω) := by
    calc
      a * Fintype.card α * bad.card = ∑ _ω ∈ bad, a * Fintype.card α := by
        simp [mul_comm]
      _ ≤ ∑ ω ∈ bad, b * emptyCount (raw ω) := by
        apply sum_le_sum
        intro ω hω
        exact (mem_filter.mp hω).2
  have hsub : (∑ ω ∈ bad, b * emptyCount (raw ω)) ≤
      ∑ ω, b * emptyCount (raw ω) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro ω _ _
    exact Nat.zero_le _
  calc
    _ ≤ a * Fintype.card α * bad.card := Nat.mul_le_mul_left _ hcount
    _ ≤ ∑ ω ∈ bad, b * emptyCount (raw ω) := hsum
    _ ≤ ∑ ω, b * emptyCount (raw ω) := hsub
    _ = b * ∑ ω, emptyCount (raw ω) := (mul_sum ..).symm

/-- Every fiber of a surjective additive group map has the kernel's cardinality. -/
theorem uniform_fibers_of_surjective {α β : Type*} [AddGroup α] [AddGroup β]
    [Fintype α] (f : α →+ β) (hf : Function.Surjective f) (y : β) :
    (univ.filter fun x ↦ f x = y).card = Fintype.card f.ker := by
  have h := Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simpa only [Fintype.card_subtype, Set.mem_preimage, Set.mem_singleton_iff] using h

/-- Equal fiber sizes give the exact change in the total number of labels. -/
theorem card_of_uniform_fibers {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : ℕ)
    (hf : ∀ y, (univ.filter fun x ↦ f x = y).card = k) :
    Fintype.card α = k * Fintype.card β := by
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset α) univ f
  simpa [hf, mul_comm] using h.symm

/-- Empty counts scale by the same fiber size as total label counts. -/
theorem emptyCount_pullback {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : ℕ)
    (hf : ∀ y, (univ.filter fun x ↦ f x = y).card = k) (n : β → ℕ) :
    emptyCount (fun x ↦ n (f x)) = k * emptyCount n := by
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset α)
    (univ.filter fun y ↦ n y = 0) f
  simpa [hf, emptyCount, mul_comm] using h.symm

/-- An exit in the quotient remains an exit after pullback to uniform raw labels. -/
theorem exit_pullback {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : ℕ)
    (hf : ∀ y, (univ.filter fun x ↦ f x = y).card = k)
    (n : β → ℕ) (a b : ℕ)
    (hexit : a * Fintype.card β ≤ b * emptyCount n) :
    a * Fintype.card α ≤ b * emptyCount (fun x ↦ n (f x)) := by
  rw [card_of_uniform_fibers f k hf, emptyCount_pullback f k hf n]
  simpa only [mul_left_comm] using Nat.mul_le_mul_left k hexit

/-- The common-witness first-moment bound with time- and input-dependent quotient labels.
Uniform fibers may change size at every entry, including when quotient rank drops. -/
theorem quotient_history_exit_first_moment {Ω ι α : Type*} [Fintype Ω] [Fintype α]
    {β : ι → Ω → Type*} [∀ i ω, Fintype (β i ω)]
    (raw : Ω → α → ℕ) (projected : ∀ i ω, β i ω → ℕ)
    (f : ∀ i ω, α → β i ω) (k : ι → Ω → ℕ)
    (fibers : ∀ i ω y, (univ.filter fun x ↦ f i ω x = y).card = k i ω)
    (gate : ι → Ω → Prop)
    (preserves : ∀ i ω, gate i ω → ∀ c, raw ω c ≠ 0 → projected i ω (f i ω c) ≠ 0)
    (a b : ℕ) :
    a * Fintype.card α *
      (univ.filter fun ω ↦ ∃ i, gate i ω ∧
        a * Fintype.card (β i ω) ≤ b * emptyCount (projected i ω)).card ≤
    b * ∑ ω, emptyCount (raw ω) := by
  have hsub :
      (univ.filter fun ω ↦ ∃ i, gate i ω ∧
        a * Fintype.card (β i ω) ≤ b * emptyCount (projected i ω)) ⊆
      (univ.filter fun ω ↦ ∃ i, gate i ω ∧
        a * Fintype.card α ≤ b * emptyCount (fun c ↦ projected i ω (f i ω c))) := by
    intro ω hω
    obtain ⟨i, hg, hi⟩ := (mem_filter.mp hω).2
    exact mem_filter.mpr ⟨mem_univ ω, i, hg,
      exit_pullback (f i ω) (k i ω) (fibers i ω) (projected i ω) a b hi⟩
  exact (Nat.mul_le_mul_left _ (card_le_card hsub)).trans
    (history_exit_first_moment raw (fun i ω c ↦ projected i ω (f i ω c))
      gate preserves a b)

end SigabaNeo.Wall1.CommonRawWitness

#print axioms SigabaNeo.Wall1.CommonRawWitness.emptyCount_le_of_preserves_hits
#print axioms SigabaNeo.Wall1.CommonRawWitness.history_exit_count_le_raw
#print axioms SigabaNeo.Wall1.CommonRawWitness.history_exit_first_moment
#print axioms SigabaNeo.Wall1.CommonRawWitness.uniform_fibers_of_surjective
#print axioms SigabaNeo.Wall1.CommonRawWitness.card_of_uniform_fibers
#print axioms SigabaNeo.Wall1.CommonRawWitness.emptyCount_pullback
#print axioms SigabaNeo.Wall1.CommonRawWitness.exit_pullback
#print axioms SigabaNeo.Wall1.CommonRawWitness.quotient_history_exit_first_moment
