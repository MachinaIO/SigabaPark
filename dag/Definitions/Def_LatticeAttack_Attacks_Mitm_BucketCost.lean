module

public import Definitions.Def_LatticeAttack_Attacks_Mitm_IndexedLookup

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.IndexedLookup

/-- Filter a bucket, counting each key equality test. -/
def filterCount {κ α : Type*} [DecidableEq κ] (q : κ) :
    List (κ × α) → List (κ × α) × Nat
  | [] => ([], 0)
  | x :: xs =>
    let (hits, tests) := filterCount q xs
    (if x.1 = q then x :: hits else hits, tests + 1)

theorem filterCount_spec {κ α : Type*} [DecidableEq κ] (q : κ) (xs : List (κ × α)) :
    filterCount q xs = (xs.filter (fun x ↦ decide (x.1 = q)), xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : x.1 = q <;> simp [filterCount, ih, h]

/-- Validity and depth alone permit arbitrarily expensive misses, even at depth zero. -/
theorem leaf_miss (n : Nat) :
    ∃ t : Tree Nat Unit, t.Valid ∧ t.depth = 0 ∧
      filterCount 1 (Tree.probe 1 t).1 = ([], n) := by
  refine ⟨.leaf (List.replicate n (0, ())), trivial, rfl, ?_⟩
  rw [filterCount_spec]
  simp [Tree.probe]

#print axioms filterCount_spec
#print axioms leaf_miss
end SigabaNeo.IndexedLookup
