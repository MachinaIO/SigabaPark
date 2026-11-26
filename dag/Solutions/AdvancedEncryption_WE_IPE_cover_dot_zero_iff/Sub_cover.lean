import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

theorem solution {A B : Type} [DecidableEq A] [DecidableEq B] (p q : ℕ) (hq : p < q)
    (L : Fin p → Finset A) (R : Fin p → Finset B) (edge : A → B → Prop)
    (cover : ∀ a b, edge a b ↔ ∃ i, a ∈ L i ∧ b ∈ R i)
    (x : A → Bool) (y : B → Bool) :
    (∑ i : Fin p, (if (∃ a ∈ L i, x a = true) then (1 : ZMod q) else 0) *
        (if (∃ b ∈ R i, y b = true) then 1 else 0)) = 0 ↔
      ¬ ∃ a b, edge a b ∧ x a = true ∧ y b = true := by
  classical
  let hits := Finset.univ.filter fun i : Fin p ↦ (∃ a ∈ L i, x a = true) ∧ (∃ b ∈ R i, y b = true)
  have hh : hits.card < q := lt_of_le_of_lt (by
    simpa using (Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin p))))) hq
  have dot : (∑ i : Fin p, (if (∃ a ∈ L i, x a = true) then (1 : ZMod q) else 0) *
        (if (∃ b ∈ R i, y b = true) then 1 else 0)) = (hits.card : ZMod q) := by
    unfold hits
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (∃ a ∈ L i, x a = true) <;> by_cases k : (∃ b ∈ R i, y b = true) <;> simp [h,k]
  rw [dot, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h hex
    obtain ⟨a,b,he,hx,hy⟩ := hex
    obtain ⟨i,hl,hr⟩ := (cover a b).mp he
    have hi : i ∈ hits := by
      simp only [hits, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨a,hl,hx⟩, ⟨b,hr,hy⟩⟩
    exact (Nat.not_le_of_gt hh) (Nat.le_of_dvd (Finset.card_pos.mpr ⟨i,hi⟩) h)
  · intro h
    suffices he : hits = ∅ by simp [he]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨a,ha,hx⟩ := hl
    obtain ⟨b,hb,hy⟩ := hr
    exact h ⟨a,b,(cover a b).mpr ⟨i,ha,hb⟩,hx,hy⟩
