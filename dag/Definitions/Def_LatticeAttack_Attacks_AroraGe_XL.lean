module

public import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

/-- Degree-t exponent vectors. -/
abbrev XLColumn (n t : ℕ) := {u : Fin n → ℕ // ∑ i, u i = t}

/-- A multiplier indexed by its exponent vector times the pivot form Y_i^d.
The row has a unit coefficient at exactly its product exponent. -/
def xlPivotEntry {K : Type*} [Zero K] [One K] {n t : ℕ}
    (d : ℕ) (i : Fin n) (v : Fin n → ℕ) (u : XLColumn n t) : K :=
  if ∀ j, v j + (if j = i then d else 0) = u.val j then 1 else 0

/-- Above the socle of the pivot complete intersection every column has a unit row. -/
theorem xl_has_unit_row {K : Type*} [Zero K] [One K] {n d t : ℕ}
    (ht : n * (d - 1) < t) (u : XLColumn n t) :
    ∃ (i : Fin n) (v : Fin n → ℕ), (∑ j, v j) + d = t ∧
      ∀ w : XLColumn n t, xlPivotEntry (K := K) d i v w = if u = w then 1 else 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d ≤ u.val i := by
    by_contra! h
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (g := fun _ : Fin n ↦ d - 1) (fun j _ ↦ Nat.le_pred_of_lt (h j))
    simp [u.property, Nat.not_le_of_gt ht] at hh
  let v := fun j ↦ u.val j - (if j = i then d else 0)
  have eqn (j : Fin n) : v j + (if j = i then d else 0) = u.val j := by
    by_cases h : j = i <;> simp_all [v]
  refine ⟨i, v, ?_, fun w ↦ ?_⟩
  · have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ eqn j)
    simpa [Finset.sum_add_distrib, u.property] using h
  · simp only [xlPivotEntry, eqn]
    have he : (∀ j, u.val j = w.val j) ↔ u = w :=
      ⟨fun h ↦ Subtype.ext (funext h), fun h ↦ h ▸ fun _ ↦ rfl⟩
    simp only [he]

/-- At the preceding degree the product of the (d-1)-st powers is a zero column. -/
theorem xl_socle_zero_column {K : Type*} [Zero K] [One K] (n d : ℕ) (hd : 0 < d) :
    ∃ u : XLColumn n (n * (d - 1)), ∀ (i : Fin n) (v : Fin n → ℕ),
      xlPivotEntry (K := K) d i v u = 0 := by
  refine ⟨⟨fun _ ↦ d - 1, by simp⟩, fun i v ↦ ?_⟩
  unfold xlPivotEntry
  split <;> rename_i h
  case isFalse => rfl
  exfalso
  have hi := h i
  simp at hi
  omega

#print axioms xl_socle_zero_column
#print axioms xl_has_unit_row

end SigabaNeo.Lattices.AroraGe
