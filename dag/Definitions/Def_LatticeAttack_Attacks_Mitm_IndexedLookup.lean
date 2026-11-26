module

public import Mathlib

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.IndexedLookup

/-- A bucket tree with exclusive upper bounds on its left branches. -/
inductive Tree (κ α : Type*) where
  | leaf (rows : List (κ × α))
  | fork (pivot : κ) (left right : Tree κ α)

namespace Tree
variable {κ α : Type*} [LinearOrder κ]

def rows : Tree κ α → List (κ × α)
  | .leaf xs => xs
  | .fork _ l r => l.rows ++ r.rows

def Valid : Tree κ α → Prop
  | .leaf _ => True
  | .fork p l r => l.Valid ∧ r.Valid ∧ (∀ x ∈ l.rows, x.1 < p) ∧ (∀ x ∈ r.rows, p ≤ x.1)

def depth : Tree κ α → Nat
  | .leaf _ => 0
  | .fork _ l r => max l.depth r.depth + 1

/-- Return the selected bucket together with the number of pivot comparisons. -/
def probe (q : κ) : Tree κ α → List (κ × α) × Nat
  | .leaf xs => (xs, 0)
  | .fork p l r =>
    let hit := if q < p then probe q l else probe q r
    (hit.1, hit.2 + 1)

theorem comparisons_le_depth (q : κ) (t : Tree κ α) : (probe q t).2 ≤ t.depth := by
  induction t with
  | leaf => simp [probe, depth]
  | fork p l r hl hr =>
    by_cases h : q < p <;> simp [probe, depth, h] <;> omega

theorem filter_probe_eq_scan (q : κ) (t : Tree κ α) (ht : t.Valid) :
    (probe q t).1.filter (fun x ↦ x.1 == q) = t.rows.filter (fun x ↦ x.1 == q) := by
  induction t with
  | leaf => rfl
  | fork p l r hl hr =>
    obtain ⟨vl, vr, lb, rb⟩ := ht
    by_cases h : q < p
    · have empty : r.rows.filter (fun x ↦ x.1 == q) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simpa using (ne_of_gt (lt_of_lt_of_le h (rb x hx)))
      simp [probe, h, rows, List.filter_append, hl vl, empty]
    · have empty : l.rows.filter (fun x ↦ x.1 == q) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simpa using (ne_of_lt (lt_of_lt_of_le (lb x hx) (le_of_not_gt h)))
      simp [probe, h, rows, List.filter_append, hr vr, empty]

#print axioms comparisons_le_depth
#print axioms filter_probe_eq_scan
end Tree
end SigabaNeo.IndexedLookup
