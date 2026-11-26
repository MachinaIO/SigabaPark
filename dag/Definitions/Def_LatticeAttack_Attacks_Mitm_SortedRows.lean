module

public import Mathlib.Data.List.Sort
public import Mathlib.Tactic

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Lattices.Mitm.SortedRows

variable {α κ : Type*} [LinearOrder κ]

/-- Sort rows while retaining their payloads, including rows sharing a key. -/
def sorted (key : α → κ) (rows : List α) : List α :=
  rows.mergeSort (fun x y ↦ decide (key x ≤ key y))

theorem sorted_pairwise (key : α → κ) (rows : List α) :
    (sorted key rows).Pairwise (fun x y ↦ key x ≤ key y) := by
  simpa [sorted] using List.pairwise_mergeSort (le := fun x y ↦ decide (key x ≤ key y))
    (by
      simpa using fun (a b c : α) ↦ @le_trans κ _ (key a) (key b) (key c))
    (by simpa using fun (a b : α) ↦ le_total (key a) (key b)) rows

theorem filter_sorted_perm (key : α → κ) (k : κ) (rows : List α) :
    ((sorted key rows).filter (fun x ↦ decide (key x = k))).Perm
      (rows.filter (fun x ↦ decide (key x = k))) :=
  (List.mergeSort_perm rows _).filter _

/-- The number of individual payloads emitted over a batch of queries. -/
def emissions (key : α → κ) (rows : List α) (queries : List κ) : ℕ :=
  (queries.map fun k ↦ (rows.filter fun x ↦ decide (key x = k)).length).sum

theorem emissions_le (key : α → κ) (rows : List α) (queries : List κ) :
    emissions key rows queries ≤ queries.length * rows.length := by
  induction queries with
  | nil => simp [emissions]
  | cons k ks ih =>
    simpa [emissions, Nat.succ_mul, Nat.add_comm] using
      Nat.add_le_add (List.length_filter_le (fun x ↦ decide (key x = k)) rows) ih

/-- Distinct payloads sharing one key saturate the product bound. -/
theorem constant_key_emissions (n t : ℕ) :
    emissions (fun _ : ℕ ↦ 0) (List.range n) (List.replicate t 0) = t * n := by
  simp [emissions]

end SigabaNeo.Lattices.Mitm.SortedRows

#print axioms SigabaNeo.Lattices.Mitm.SortedRows.sorted_pairwise
#print axioms SigabaNeo.Lattices.Mitm.SortedRows.filter_sorted_perm
#print axioms SigabaNeo.Lattices.Mitm.SortedRows.emissions_le
#print axioms SigabaNeo.Lattices.Mitm.SortedRows.constant_key_emissions
