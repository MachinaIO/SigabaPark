module

public import Definitions.Def_LatticeAttack_Algorithms_SortedJoin

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.SortedJoin

open Lattices.Mitm.SortedRows

variable {α β κ : Type*} [LinearOrder κ]

def pairBatch (key : α → κ) (a : Array α) : List (β × κ) → List (β × α) × ℕ
  | [] => ([], 0)
  | (b, k) :: qs =>
    let p := probe key a k
    let t := pairBatch key a qs
    (p.1.map (b, ·) ++ t.1, p.2 + t.2)

/-- Sort the rows once and attach each query's payload to every matching row. -/
def pairJoin (key : α → κ) (rows : List α) (qs : List (β × κ)) : List (β × α) × ℕ :=
  let s := sort (fun x y ↦ decide (key x ≤ key y)) (Nat.clog 2 (rows.length + 1)) rows
  let t := pairBatch key s.1.toArray qs
  (t.1, s.2 + t.2)

theorem pairJoin_spec (key : α → κ) (rows : List α) (qs : List (β × κ)) :
    (pairJoin key rows qs).1.Perm
      (qs.flatMap fun (b, k) ↦ (rows.filter (key · = k)).map (b, ·)) ∧
    (pairJoin key rows qs).2 ≤ rows.length * Nat.clog 2 (rows.length + 1) +
      qs.length * (Nat.clog 2 (rows.length + 1) + 1) + (pairJoin key rows qs).1.length := by
  let xs := sorted key rows
  let d := Nat.clog 2 (rows.length + 1)
  obtain ⟨es, cs⟩ := sort_spec (fun x y ↦ decide (key x ≤ key y)) d rows
    (by dsimp [d]; have := Nat.le_pow_clog (by decide : 1 < 2) (rows.length + 1); omega)
  change _ = xs at es
  have hl : xs.length = rows.length := List.length_mergeSort ..
  have hb : (pairBatch key xs.toArray qs).1.Perm
        (qs.flatMap fun (b, k) ↦ (rows.filter (key · = k)).map (b, ·)) ∧
      (pairBatch key xs.toArray qs).2 ≤ qs.length * (d + 1) +
        (pairBatch key xs.toArray qs).1.length := by
    induction qs with
    | nil => simp [pairBatch]
    | cons q qs ih =>
      obtain ⟨b, k⟩ := q
      obtain ⟨ep, cp⟩ := probe_spec key xs k (sorted_pairwise key rows)
      have hp : (probe key xs.toArray k).1.Perm (rows.filter (key · = k)) := by
        rw [ep]
        exact filter_sorted_perm key k rows
      refine ⟨(hp.map (b, ·)).append ih.1, ?_⟩
      rw [hl] at cp
      change _ ≤ d + 1 + _ at cp
      have ht := ih.2
      simp only [pairBatch, List.length_cons, Nat.succ_mul, List.length_append, List.length_map]
      omega
  dsimp [d] at es cs hb
  simp only [pairJoin, es]
  exact ⟨hb.1, by have := Nat.add_le_add cs hb.2; omega⟩

#print axioms pairJoin_spec

end SigabaNeo.SortedJoin
