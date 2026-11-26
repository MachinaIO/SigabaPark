import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith

theorem solution {Ω ι X : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Ω → ι → X) (S : Finset ι) (N : ℕ) (hΩ : Fintype.card Ω ≤ 2 ^ N)
    (hfresh : ∀ ω, ∀ w ∈ S, ∃ ω', Y ω' w ≠ Y ω w ∧ ∀ v, v ≠ w → Y ω' v = Y ω v) :
    S.card ≤ N := by
  classical
  have gen : ∀ (S : Finset ι) (P : Finset (ι → X)), P.Nonempty →
      (∀ g ∈ P, ∀ w ∈ S, ∃ g' ∈ P, g' w ≠ g w ∧ ∀ v, v ≠ w → g' v = g v) →
      2 ^ S.card ≤ P.card := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro P hne _; simpa using Finset.card_pos.mpr hne
    | insert a S ha ih =>
      intro P hne hfresh
      obtain ⟨g, hg⟩ := hne
      obtain ⟨g', hg', hne', -⟩ := hfresh g hg a (Finset.mem_insert_self a S)
      have key : ∀ x, (P.filter (fun f => f a = x)).Nonempty →
          2 ^ S.card ≤ (P.filter (fun f => f a = x)).card := by
        intro x hx
        apply ih _ hx
        intro f hf w hw
        rw [Finset.mem_filter] at hf
        obtain ⟨f', hf', h1, h2⟩ := hfresh f hf.1 w (Finset.mem_insert_of_mem hw)
        have hwa : w ≠ a := fun h => ha (h ▸ hw)
        refine ⟨f', Finset.mem_filter.mpr ⟨hf', ?_⟩, h1, h2⟩
        rw [h2 a (Ne.symm hwa)]; exact hf.2
      have h1 := key (g a) ⟨g, Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
      have h2 := key (g' a) ⟨g', Finset.mem_filter.mpr ⟨hg', rfl⟩⟩
      have hdisj : Disjoint (P.filter (fun f => f a = g a)) (P.filter (fun f => f a = g' a)) := by
        rw [Finset.disjoint_filter]; intro f _ h h'; exact hne' (h'.symm.trans h)
      have hsub : (P.filter (fun f => f a = g a)) ∪ (P.filter (fun f => f a = g' a)) ⊆ P := by
        intro f hf; rcases Finset.mem_union.mp hf with h | h <;> exact (Finset.mem_filter.mp h).1
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at this
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      omega
  have h := gen S (Finset.univ.image Y) (Finset.univ_nonempty.image Y) (by
      intro g hg w hw
      obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨ω', h1, h2⟩ := hfresh ω w hw
      exact ⟨Y ω', Finset.mem_image_of_mem Y (Finset.mem_univ _), h1, h2⟩)
  have h2 := Finset.card_image_le (s := Finset.univ) (f := Y)
  rw [Finset.card_univ] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h.trans (h2.trans hΩ))
